"""
AgenticLoopBase - Base class for agentic workflows with function calling

This base class provides the core agent loop logic.
Subclasses specify which tools are available to the agent.

Key characteristics:
- Function calling / tool use
- Agent autonomy in strategy
- Limited only by compilation count
- Flexible tool composition
"""

import time
import json
from typing import List, Dict, Any, Optional
from abc import abstractmethod
from .base import BaseWorkflow, WorkflowResult, FixAttempt


class AgenticLoopBase(BaseWorkflow):
    """
    Base class for agent workflows with function calling

    Subclasses override _get_available_tools() to specify tool set.
    """

    def __init__(self, llm_client, max_compilations: int = 3, workflow_name: str = "agentic"):
        super().__init__(
            llm_client=llm_client,
            max_compilations=max_compilations,
            workflow_name=workflow_name
        )
        self.max_iterations = max_compilations * 20  # Safety limit

    @abstractmethod
    def _get_available_tools(self) -> List[str]:
        """
        Specify which tools are available to the agent

        Returns:
            List of tool names (e.g., ['compile', 'read', 'write', 'rag'])
        """
        pass

    def _fix_spec_implementation(self, work_spec_path: str) -> WorkflowResult:
        """
        Fix spec using agentic approach with function calling

        Args:
            work_spec_path: Path to working copy of .tla file

        Returns:
            WorkflowResult with execution details
        """
        spec_path = work_spec_path  # Rename for consistency with rest of code
        print(f"\n{'='*80}")
        print(f"[{self.workflow_name}] Starting repair: {spec_path}")
        print(f"Max compilations: {self.max_compilations}")
        print(f"Available tools: {', '.join(self._get_available_tools())}")
        print('='*80)

        start_time = time.time()
        self._reset_counters()
        attempts = []

        # Initialize conversation
        system_prompt = self._create_system_prompt(spec_path)
        conversation = [{"role": "system", "content": system_prompt}]

        # Add initial task message
        initial_message = f"Please fix all compilation errors in {spec_path}. Start by checking compilation status."
        conversation.append({"role": "user", "content": initial_message})

        # Agent loop
        iterations = 0
        last_error_count = None
        max_cleanup_iterations = 3  # After compilation limit, allow 3 more iterations
        cleanup_iterations = 0
        in_cleanup_phase = False

        while iterations < self.max_iterations:
            iterations += 1

            # Check if entered cleanup phase
            if self.compilation_count >= self.max_compilations and not in_cleanup_phase:
                in_cleanup_phase = True
                print(f"\n⚠️  Compilation limit reached ({self.max_compilations}/{self.max_compilations})")
                print(f"   Entering cleanup phase: {max_cleanup_iterations} more iterations allowed")
                print(f"   Agent can still read/write/rag_search, but cannot compile anymore")

            # Check cleanup limit
            if in_cleanup_phase:
                cleanup_iterations += 1
                if cleanup_iterations > max_cleanup_iterations:
                    print(f"\n⚠️  Cleanup iterations exhausted ({cleanup_iterations-1}/{max_cleanup_iterations})")
                    break
                print(f"\n--- Agent Iteration {iterations} [CLEANUP {cleanup_iterations}/{max_cleanup_iterations}] ---")
            else:
                print(f"\n--- Agent Iteration {iterations} ---")

            # Add cleanup reminder to conversation if in cleanup phase
            if in_cleanup_phase and cleanup_iterations == 1:
                # Add a system message to remind LLM
                cleanup_reminder = {
                    "role": "user",
                    "content": f"""IMPORTANT NOTICE: Compilation budget exhausted ({self.max_compilations}/{self.max_compilations} used).
You have {max_cleanup_iterations} more iterations to make final fixes.
- You CANNOT use tla_compile anymore (it will fail)
- You CAN still use: read, write, rag_search
- Make your best final attempt to fix the errors
- After {max_cleanup_iterations} iterations, the process will stop"""
                }
                conversation.append(cleanup_reminder)

            # LLM decision
            if in_cleanup_phase:
                print(f"[LLM] Making decision (call #{self.llm_call_count + 1}) [Cleanup {cleanup_iterations}/{max_cleanup_iterations}]...")
            else:
                print(f"[LLM] Making decision (call #{self.llm_call_count + 1})...")
            try:
                response = self.llm.get_completion_with_tools(
                    messages=conversation,
                    tools=self._get_tool_schemas()
                )
                self.llm_call_count += 1

            except Exception as e:
                print(f"✗ LLM call failed: {e}")
                break

            # Check if LLM wants to stop (no tool calls)
            if not response.get('tool_calls'):
                print("[LLM] No tool calls - agent finished")
                break

            # Execute tool calls
            tool_calls = response.get('tool_calls', [])
            print(f"[Tools] Executing {len(tool_calls)} tool call(s)...")
            tool_results = []

            for tool_call in tool_calls:
                result = self._execute_tool_call(tool_call, spec_path)
                tool_results.append(result)

                # Check if compilation succeeded
                if hasattr(tool_call, 'function'):
                    check_tool_name = tool_call.function.name
                else:
                    check_tool_name = tool_call.get('function', {}).get('name') or tool_call.get('name')

                if check_tool_name == 'tla_compile' and result.get('success'):
                    error_count = result.get('error_count', 0)
                    if error_count == 0:
                        print("✓ Compilation successful! All errors fixed.")

                        attempts.append(FixAttempt(
                            iteration=iterations,
                            errors_before=[] if last_error_count is None else [],
                            error_count_before=last_error_count or 0,
                            action_description="Agent achieved successful compilation",
                            errors_after=[],
                            error_count_after=0,
                            improved=True,
                            compilation_time=result.get('compilation_time', 0.0)
                        ))

                        return self._create_result(
                            spec_path=spec_path,
                            success=True,
                            attempts=attempts,
                            total_time=time.time() - start_time,
                            final_error_count=0,
                            final_errors=[]
                        )
                    else:
                        last_error_count = error_count

            # Add assistant response with tool uses
            # Format depends on provider (OpenAI vs Anthropic)
            if self.llm.provider == 'openai':
                # OpenAI format: tool_calls at message level
                assistant_message = {
                    "role": "assistant",
                    "content": response.get('text') or None,
                    "tool_calls": []
                }

                for tool_call in tool_calls:
                    # Support both object and dict formats
                    if hasattr(tool_call, 'function'):
                        # Already in OpenAI format
                        assistant_message["tool_calls"].append({
                            "id": tool_call.id,
                            "type": "function",
                            "function": {
                                "name": tool_call.function.name,
                                "arguments": tool_call.function.arguments if isinstance(tool_call.function.arguments, str) else json.dumps(tool_call.function.arguments)
                            }
                        })
                    else:
                        # Convert from dict format
                        tool_id = tool_call.get('id')
                        tool_name = tool_call.get('name')
                        tool_args = tool_call.get('arguments', {})
                        assistant_message["tool_calls"].append({
                            "id": tool_id,
                            "type": "function",
                            "function": {
                                "name": tool_name,
                                "arguments": json.dumps(tool_args) if not isinstance(tool_args, str) else tool_args
                            }
                        })

                conversation.append(assistant_message)

                # Add tool results - OpenAI uses "tool" role
                for tool_call, result in zip(tool_calls, tool_results):
                    if hasattr(tool_call, 'id'):
                        tool_call_id = tool_call.id
                    else:
                        tool_call_id = tool_call.get('id')

                    conversation.append({
                        "role": "tool",
                        "tool_call_id": tool_call_id,
                        "content": json.dumps(result)
                    })

            else:
                # Anthropic format: tool_use in content array
                assistant_content = []
                if response.get('text'):
                    assistant_content.append({"type": "text", "text": response.get('text')})

                for tool_call in tool_calls:
                    # Support both object and dict formats
                    if hasattr(tool_call, 'function'):
                        tool_id = tool_call.id
                        tool_name = tool_call.function.name
                        tool_args = tool_call.function.arguments
                    else:
                        tool_id = tool_call.get('id')
                        tool_name = tool_call.get('name')
                        tool_args = tool_call.get('arguments', {})

                    assistant_content.append({
                        "type": "tool_use",
                        "id": tool_id,
                        "name": tool_name,
                        "input": tool_args
                    })

                conversation.append({
                    "role": "assistant",
                    "content": assistant_content
                })

                # Add tool results as user message - Anthropic format
                tool_result_content = []
                for tool_call, result in zip(tool_calls, tool_results):
                    # Support both object and dict formats
                    if hasattr(tool_call, 'id'):
                        tool_use_id = tool_call.id
                    else:
                        tool_use_id = tool_call.get('id')

                    tool_result_content.append({
                        "type": "tool_result",
                        "tool_use_id": tool_use_id,
                        "content": json.dumps(result)
                    })

                conversation.append({
                    "role": "user",
                    "content": tool_result_content
                })

        # Failed to fix
        print(f"\n✗ Failed to fix all errors")
        print(f"   Used {self.compilation_count}/{self.max_compilations} compilations")
        print(f"   Used {iterations} agent iterations")

        # Final check
        final_compile = self.compile_tool.run(spec_path)
        final_error_count = final_compile.data.get('error_count', last_error_count or 0)
        final_errors = final_compile.data.get('error_messages', [])

        return self._create_result(
            spec_path=spec_path,
            success=False,
            attempts=attempts,
            total_time=time.time() - start_time,
            final_error_count=final_error_count,
            final_errors=final_errors
        )

    def _create_system_prompt(self, spec_path: str) -> str:
        """Create system prompt for agent"""
        module_name = self._extract_module_name(spec_path)
        available_tools = self._get_available_tools()

        # Base tools description
        tools_desc = """AVAILABLE TOOLS:
1. tla_compile(spec_path): Check if spec compiles, get error messages
   - IMPORTANT: Limited to {max_comp} uses total!
   - Use wisely - compile only when you want to verify changes

2. read(file_path): Read the current spec content

3. write(file_path, content): Write a new version of the spec
   - OVERWRITES the entire file with provided content
   - You MUST provide the COMPLETE file content (not a diff or patch)
   - File must already exist""".format(max_comp=self.max_compilations)

        # Add RAG tool if available
        if 'rag' in available_tools:
            tools_desc += """

4. rag_search(error_message, top_k): Search for similar errors and solutions
   - Use when you encounter unfamiliar error patterns
   - Returns examples of similar errors and how they were fixed"""

        return f"""You are a TLA+ syntax expert helping to fix compilation errors.

FILE: {spec_path}
MODULE NAME: {module_name}

{tools_desc}

STRATEGY:
- Start by compiling to see what errors exist
- Read the spec to understand it
- Analyze ALL errors carefully
- Fix ALL errors at once and write the complete fixed spec
- Compile to verify your changes
- If errors remain, repeat the process

IMPORTANT:
- The MODULE name must match the filename: {module_name}
- Compilation budget is LIMITED ({self.max_compilations} times) - use it wisely!
- Try to fix all errors in one write to save compilation budget
- Only do incremental fixes if the errors are too complex or numerous
- Stop when compilation succeeds (0 errors)

Begin by checking the compilation status."""

    def _get_tool_schemas(self) -> List[Dict[str, Any]]:
        """Get tool schemas for function calling based on available tools"""
        available_tools = self._get_available_tools()
        schemas = []

        if 'compile' in available_tools:
            schemas.append({
                "type": "function",
                "function": {
                    "name": "tla_compile",
                    "description": f"Check if TLA+ spec compiles and get error messages. LIMITED: Can only use {self.max_compilations - self.compilation_count} more times!",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "spec_path": {
                                "type": "string",
                                "description": "Path to the .tla file"
                            }
                        },
                        "required": ["spec_path"]
                    }
                }
            })

        if 'read' in available_tools:
            schemas.append({
                "type": "function",
                "function": {
                    "name": "read",
                    "description": "Read a file and return its content",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "file_path": {
                                "type": "string",
                                "description": "Path to the file"
                            }
                        },
                        "required": ["file_path"]
                    }
                }
            })

        if 'write' in available_tools:
            schemas.append({
                "type": "function",
                "function": {
                    "name": "write",
                    "description": "Write complete file content to an existing file. OVERWRITES entire file - you must provide the full spec, not a diff.",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "file_path": {
                                "type": "string",
                                "description": "Path to the file (must exist)"
                            },
                            "content": {
                                "type": "string",
                                "description": "COMPLETE file content (entire spec from beginning to end)"
                            }
                        },
                        "required": ["file_path", "content"]
                    }
                }
            })

        if 'rag' in available_tools:
            schemas.append({
                "type": "function",
                "function": {
                    "name": "rag_search",
                    "description": "Search for similar TLA+ compilation errors and their solutions from knowledge base",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "error_message": {
                                "type": "string",
                                "description": "The error message to search for"
                            },
                            "top_k": {
                                "type": "integer",
                                "description": "Number of similar examples to return (default: 3)",
                                "default": 3
                            }
                        },
                        "required": ["error_message"]
                    }
                }
            })

        return schemas

    def _execute_tool_call(self, tool_call, spec_path: str) -> Dict[str, Any]:
        """
        Execute a tool call and return result as dict

        Args:
            tool_call: Tool call from LLM (dict or object)
            spec_path: Spec path for context

        Returns:
            Dict with tool result
        """
        # Support both dict and object formats (OpenAI vs Anthropic)
        if hasattr(tool_call, 'function'):
            # OpenAI object format
            tool_name = tool_call.function.name
            arguments = tool_call.function.arguments
            tool_id = tool_call.id
        elif isinstance(tool_call, dict):
            # Dict format (from Anthropic or our own processing)
            tool_name = tool_call.get('function', {}).get('name') or tool_call.get('name')
            arguments = tool_call.get('function', {}).get('arguments') or tool_call.get('arguments', {})
            tool_id = tool_call.get('id')
        else:
            return {"success": False, "error": "Unknown tool_call format"}

        # Parse arguments if string
        if isinstance(arguments, str):
            try:
                arguments = json.loads(arguments)
            except:
                return {"success": False, "error": "Invalid arguments"}

        print(f"      → {tool_name}({', '.join(f'{k}={v[:50]}...' if len(str(v)) > 50 else f'{k}={v}' for k, v in arguments.items())})")

        try:
            if tool_name == "tla_compile":
                # Check limit
                if self.compilation_count >= self.max_compilations:
                    return {
                        "success": False,
                        "error": f"❌ Compilation limit reached ({self.max_compilations}/{self.max_compilations} used). You CANNOT compile anymore. Please use read/write to make final fixes without compiling.",
                        "error_count": -1,
                        "compilations_remaining": 0
                    }

                result = self.compile_with_limit(arguments['spec_path'])
                if result is None:
                    return {
                        "success": False,
                        "error": f"Compilation limit reached",
                        "error_count": -1
                    }

                return {
                    "success": result.success,
                    "error_count": result.data.get('error_count', 0),
                    "error_messages": result.data.get('error_messages', []),
                    "compilation_time": result.data.get('compilation_time', 0.0),
                    "compilations_remaining": self.max_compilations - self.compilation_count
                }

            elif tool_name == "read":
                result = self.read_spec(arguments['file_path'])
                if result.success:
                    return {
                        "success": True,
                        "content": result.data,
                        "file_path": arguments['file_path']
                    }
                else:
                    return {
                        "success": False,
                        "error": result.error
                    }

            elif tool_name == "write":
                result = self.write_spec(arguments['file_path'], arguments['content'])
                return {
                    "success": result.success,
                    "message": result.data if result.success else result.error
                }

            elif tool_name == "rag_search":
                # RAG search will be implemented by subclasses that need it
                return self._execute_rag_search(arguments)

            else:
                return {
                    "success": False,
                    "error": f"Unknown tool: {tool_name}"
                }

        except Exception as e:
            return {
                "success": False,
                "error": f"Tool execution error: {str(e)}"
            }

    def _execute_rag_search(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """
        Execute RAG search (override in subclasses that support RAG)

        Args:
            arguments: Dict with 'error_message' and optional 'top_k'

        Returns:
            Dict with search results
        """
        return {
            "success": False,
            "error": "RAG search not available in this workflow"
        }

    def _create_result(self, spec_path: str, success: bool, attempts: List[FixAttempt],
                      total_time: float, final_error_count: int, final_errors: List[str]) -> WorkflowResult:
        """Create WorkflowResult from execution data"""
        return WorkflowResult(
            spec_path=spec_path,
            workflow_name=self.workflow_name,
            success=success,
            compilations_used=self.compilation_count,
            iterations=len(attempts) if attempts else self.llm_call_count,
            llm_calls=self.llm_call_count,
            tool_calls_total=self.tool_call_count,
            total_time=total_time,
            attempts=attempts,
            total_tokens=self.total_tokens,
            prompt_tokens=self.prompt_tokens,
            completion_tokens=self.completion_tokens,
            final_error_count=final_error_count,
            final_errors=final_errors
        )
