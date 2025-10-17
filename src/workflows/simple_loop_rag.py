"""
SimpleLoop_RAG Workflow - Simple iterative repair with RAG support

This workflow extends SimpleLoop by adding RAG (Retrieval-Augmented Generation):
- Same fixed flow as SimpleLoop: Compile → Read → LLM Fix → Write
- Enhanced with automatic error pattern search before each LLM call
- Provides example solutions to the LLM based on similar past errors

Key differences from SimpleLoop:
- Automatically retrieves similar errors and solutions before calling LLM
- Enriches LLM prompt with example solutions
- No agent autonomy (RAG is automatic, not agent-controlled)

Key differences from AgenticLoop_RAG:
- Fixed deterministic flow (not agentic)
- RAG is automatically applied on every fix attempt
- Agent doesn't decide when to use RAG
"""

from typing import List
from pathlib import Path
from .simple_loop import SimpleLoop
from ..rag.retriever import ErrorRetriever


class SimpleLoop_RAG(SimpleLoop):
    """
    Simple iterative repair workflow with automatic RAG support

    Each iteration:
    - Compile → Read → RAG Search → LLM Fix (with examples) → Write
    """

    def __init__(self, llm_client, max_compilations: int = 3, knowledge_base_path: str = None):
        super().__init__(
            llm_client=llm_client,
            max_compilations=max_compilations
        )

        # Override workflow name
        self.workflow_name = "simple_loop_rag"

        # Initialize RAG retriever
        if knowledge_base_path is None:
            # Try to get from config
            from ..utils.config import get_config
            config = get_config()
            kb_default = config.get('paths.knowledge_base', 'src/rag/initial_errors.json')

            # Convert to absolute path based on project root
            if not Path(kb_default).is_absolute():
                project_root = Path(__file__).parent.parent.parent
                knowledge_base_path = str(project_root / kb_default)
            else:
                knowledge_base_path = kb_default

        kb_path = Path(knowledge_base_path)
        if not kb_path.exists():
            raise FileNotFoundError(f"Knowledge base not found: {knowledge_base_path}")

        print(f"Loading RAG knowledge base from: {knowledge_base_path}")
        self.retriever = ErrorRetriever(str(kb_path))
        self.rag_searches = 0  # Track RAG searches

    def _call_llm_to_fix(self, spec_path: str, spec_content: str, errors: List[str]) -> str:
        """
        Call LLM to generate a fixed version of the spec
        Enhanced with RAG: automatically retrieves similar errors and solutions

        Args:
            spec_path: Path to spec (for context)
            spec_content: Current spec content
            errors: List of compilation errors

        Returns:
            Fixed spec content, or None if LLM call failed
        """
        module_name = self._extract_module_name(spec_path)
        errors_formatted = self._format_errors_for_llm(errors)

        # ====== RAG ENHANCEMENT: Retrieve similar errors ======
        rag_examples = self._retrieve_similar_errors(errors)

        # Format RAG examples for prompt
        rag_context = self._format_rag_examples(rag_examples)

        # ====== Enhanced System Prompt with RAG ======
        system_prompt = f"""You are a TLA+ syntax expert. Fix all compilation errors in the specification.

IMPORTANT:
1. The MODULE name MUST match the filename: {module_name}
2. Return ONLY the complete fixed specification
3. Do NOT include explanations or markdown code blocks
4. The output should start with "---- MODULE {module_name} ----"

{rag_context}"""

        # User content (same as SimpleLoop)
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

    def _retrieve_similar_errors(self, errors: List[str], top_k: int = 3) -> List[dict]:
        """
        Retrieve similar errors and their solutions from knowledge base

        Args:
            errors: List of compilation error messages
            top_k: Number of similar errors to retrieve per error

        Returns:
            List of retrieval results
        """
        all_results = []

        # Search for each error
        for error in errors:
            try:
                results = self.retriever.search(error, top_k=top_k)
                all_results.extend(results)
                self.rag_searches += 1
            except Exception as e:
                print(f"    Warning: RAG search failed for error: {e}")
                continue

        # Remove duplicates and sort by similarity
        seen_ids = set()
        unique_results = []
        for result in all_results:
            error_id = result.get('error_id', '')
            if error_id and error_id not in seen_ids:
                seen_ids.add(error_id)
                unique_results.append(result)

        # Sort by similarity score and take top results
        unique_results.sort(key=lambda x: x.get('similarity_score', 0), reverse=True)

        return unique_results[:top_k * 2]  # Return more examples for better coverage

    def _format_rag_examples(self, rag_results: List[dict]) -> str:
        """
        Format RAG retrieval results for LLM prompt

        Args:
            rag_results: List of retrieval results

        Returns:
            Formatted string for prompt
        """
        if not rag_results:
            return ""

        examples_text = "\n📚 REFERENCE EXAMPLES FROM KNOWLEDGE BASE:\n"
        examples_text += "Here are similar errors encountered before and how they were fixed:\n\n"

        for i, result in enumerate(rag_results, 1):
            similarity = result.get('similarity_score', 0.0)
            error_pattern = result.get('error_message', 'Unknown error')
            solution = result.get('solution', 'No solution available')
            context = result.get('context', '')

            examples_text += f"Example {i} (similarity: {similarity:.2f}):\n"
            examples_text += f"  Error Pattern: {error_pattern}\n"
            if context:
                examples_text += f"  Context: {context}\n"
            examples_text += f"  Solution: {solution}\n"
            examples_text += "\n"

        examples_text += "Use these examples as reference when fixing the current errors.\n"

        return examples_text
