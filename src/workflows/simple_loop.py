"""
SimpleLoop Workflow - Simple iterative repair with fixed flow

This workflow follows a deterministic, fixed-step process:
1. Compile to check for errors
2. If errors exist, read the spec
3. Call LLM once to generate a fix
4. Write the fixed spec
5. Repeat until success or max compilations reached

Key characteristics:
- Deterministic flow (same steps every iteration)
- One LLM call per iteration
- All errors fixed at once (not incremental)
- No agent autonomy
"""

import time
from typing import List
from .base import BaseWorkflow, WorkflowResult, FixAttempt


class SimpleLoop(BaseWorkflow):
    """
    Simple iterative repair workflow with fixed steps

    Each iteration:
    - Compile → Read → LLM Fix → Write
    """

    def __init__(self, llm_client, max_compilations: int = 3):
        super().__init__(
            llm_client=llm_client,
            max_compilations=max_compilations,
            workflow_name="simple_loop"
        )

    def _fix_spec_implementation(self, work_spec_path: str) -> WorkflowResult:
        """
        Fix spec using simple iterative approach

        Args:
            work_spec_path: Path to working copy of .tla file

        Returns:
            WorkflowResult with execution details
        """
        spec_path = work_spec_path  # Rename for consistency with rest of code
        print(f"\n{'='*80}")
        print(f"[SimpleLoop] Starting repair: {spec_path}")
        print(f"Max compilations: {self.max_compilations}")
        print('='*80)

        start_time = time.time()
        self._reset_counters()
        attempts = []

        # Iterative repair loop
        for iteration in range(self.max_compilations):
            print(f"\n--- Iteration {iteration + 1}/{self.max_compilations} ---")

            # Step 1: Compile
            print(f"[1/4] Compiling (attempt {self.compilation_count + 1}/{self.max_compilations})...")
            compile_result = self.compile_with_limit(spec_path)

            if compile_result is None:
                print("⚠️  Compilation limit reached!")
                break

            errors_before = compile_result.data.get('error_messages', [])
            error_count_before = compile_result.data.get('error_count', 0)
            compilation_time = compile_result.data.get('compilation_time', 0.0)

            print(f"    Errors found: {error_count_before}")

            # Step 2: Check success
            if compile_result.success:
                print("✓ Compilation successful! All errors fixed.")

                attempts.append(FixAttempt(
                    iteration=iteration + 1,
                    errors_before=errors_before,
                    error_count_before=error_count_before,
                    action_description="Compilation successful",
                    errors_after=[],
                    error_count_after=0,
                    improved=True,
                    compilation_time=compilation_time
                ))

                return self._create_result(
                    spec_path=spec_path,
                    success=True,
                    attempts=attempts,
                    total_time=time.time() - start_time,
                    final_error_count=0,
                    final_errors=[]
                )

            # Step 3: Read current spec
            print("[2/4] Reading spec...")
            read_result = self.read_spec(spec_path)

            if not read_result.success:
                print(f"✗ Failed to read spec: {read_result.error}")
                break

            spec_content = read_result.data
            print(f"    Spec length: {len(spec_content)} chars")

            # Step 4: LLM fix
            print("[3/4] Calling LLM to generate fix...")
            fixed_content = self._call_llm_to_fix(
                spec_path=spec_path,
                spec_content=spec_content,
                errors=errors_before
            )

            if fixed_content is None:
                print("✗ LLM failed to generate fix")
                break

            print(f"    Generated fix: {len(fixed_content)} chars")

            # Step 5: Write fixed spec
            print("[4/4] Writing fixed spec...")
            write_result = self.write_spec(spec_path, fixed_content)

            if not write_result.success:
                print(f"✗ Failed to write spec: {write_result.error}")
                break

            print("    Written successfully")

            # Record this attempt
            attempts.append(FixAttempt(
                iteration=iteration + 1,
                errors_before=errors_before,
                error_count_before=error_count_before,
                action_description=f"LLM fix applied (iteration {iteration + 1})",
                errors_after=[],  # Will check in next iteration
                error_count_after=error_count_before,  # Unknown until next compile
                improved=False,  # Unknown until next compile
                compilation_time=compilation_time
            ))

            # Check if stuck
            if self._is_stuck(attempts):
                print("⚠️  Detected stuck in loop (same errors repeatedly)")
                break

        # Failed to fix within compilation limit
        print(f"\n✗ Failed to fix all errors within {self.max_compilations} compilations")

        # Do a final check to get actual error count
        final_compile = self.compile_tool.run(spec_path)
        final_error_count = final_compile.data.get('error_count', error_count_before)
        final_errors = final_compile.data.get('error_messages', errors_before)

        return self._create_result(
            spec_path=spec_path,
            success=False,
            attempts=attempts,
            total_time=time.time() - start_time,
            final_error_count=final_error_count,
            final_errors=final_errors
        )

    def _call_llm_to_fix(self, spec_path: str, spec_content: str, errors: List[str]) -> str:
        """
        Call LLM to generate a fixed version of the spec

        Args:
            spec_path: Path to spec (for context)
            spec_content: Current spec content
            errors: List of compilation errors

        Returns:
            Fixed spec content, or None if LLM call failed
        """
        module_name = self._extract_module_name(spec_path)
        errors_formatted = self._format_errors_for_llm(errors)

        # System prompt
        system_prompt = f"""You are a TLA+ syntax expert. Fix all compilation errors in the specification.

IMPORTANT:
1. The MODULE name MUST match the filename: {module_name}
2. Return ONLY the complete fixed specification
3. Do NOT include explanations or markdown code blocks
4. The output should start with "---- MODULE {module_name} ----"
"""

        # User content
        user_content = f"""SPECIFICATION FILE: {module_name}.tla

COMPILATION ERRORS:
{errors_formatted}

CURRENT SPECIFICATION:
```tla
{spec_content}
```

Please fix ALL errors in one go and return the complete fixed specification."""

        try:
            # Call LLM using Specula's LLMClient
            response_text = self.llm.get_completion(system_prompt, user_content)
            self.llm_call_count += 1

            # Extract fixed spec from response
            fixed_spec = self._extract_spec_from_response(response_text)

            return fixed_spec

        except Exception as e:
            print(f"    Error calling LLM: {e}")
            return None

    def _extract_spec_from_response(self, response_text: str) -> str:
        """
        Extract TLA+ spec from LLM response

        Handles cases where LLM might include markdown code blocks or explanations.

        Args:
            response_text: Raw LLM response

        Returns:
            Extracted spec content
        """
        # Remove markdown code blocks if present
        text = response_text.strip()

        # Check for ```tla ... ``` or ```... ```
        if '```' in text:
            # Find first code block
            parts = text.split('```')
            for i, part in enumerate(parts):
                if i % 2 == 1:  # Odd indices are code blocks
                    # Remove language identifier if present
                    lines = part.strip().split('\n')
                    if lines[0].strip() in ['tla', 'TLA+', 'tlaplus']:
                        return '\n'.join(lines[1:])
                    return part.strip()

        # No code blocks, check if starts with MODULE
        if '---- MODULE' in text:
            # Find the start of the module
            module_start = text.find('---- MODULE')
            return text[module_start:].strip()

        # Return as-is
        return text.strip()

    def _create_result(self, spec_path: str, success: bool, attempts: List[FixAttempt],
                      total_time: float, final_error_count: int, final_errors: List[str]) -> WorkflowResult:
        """Create WorkflowResult from execution data"""
        return WorkflowResult(
            spec_path=spec_path,
            workflow_name=self.workflow_name,
            success=success,
            compilations_used=self.compilation_count,
            iterations=len(attempts),
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
