"""
AgenticLoop_RAG Workflow - Agentic workflow with RAG support

This workflow extends AgenticLoop by adding RAG (Retrieval-Augmented Generation):
- All basic tools (compile, read, write)
- rag_search: Search for similar errors and solutions

The agent can autonomously decide when to search the knowledge base
for examples of similar errors and their fixes.
"""

from typing import List, Dict, Any
from pathlib import Path
from .agentic_loop_base import AgenticLoopBase
from ..rag.retriever import ErrorRetriever


class AgenticLoop_RAG(AgenticLoopBase):
    """
    Agentic workflow with RAG tool for error pattern search
    """

    def __init__(self, llm_client, max_compilations: int = 3, knowledge_base_path: str = None):
        super().__init__(
            llm_client=llm_client,
            max_compilations=max_compilations,
            workflow_name="agentic_loop_rag"
        )

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

    def _get_available_tools(self) -> List[str]:
        """Extended tool set: compile, read, write, rag"""
        return ['compile', 'read', 'write', 'rag']

    def _execute_rag_search(self, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """
        Execute RAG search for similar errors

        Args:
            arguments: Dict with 'error_message' and optional 'top_k'

        Returns:
            Dict with search results
        """
        try:
            error_message = arguments.get('error_message', '')
            top_k = arguments.get('top_k', 3)

            if not error_message:
                return {
                    "success": False,
                    "error": "error_message is required"
                }

            # Search for similar errors
            results = self.retriever.search(error_message, top_k=top_k)

            # Format results
            formatted_results = []
            for result in results:
                formatted_results.append({
                    "error_id": result.get('error_id', 'unknown'),
                    "similarity": result.get('similarity_score', 0.0),
                    "error_pattern": result.get('error_message', ''),
                    "solution": result.get('solution', ''),
                    "context": result.get('context', '')
                })

            return {
                "success": True,
                "results": formatted_results,
                "count": len(formatted_results)
            }

        except Exception as e:
            return {
                "success": False,
                "error": f"RAG search failed: {str(e)}"
            }
