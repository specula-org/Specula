import logging
import subprocess
from pathlib import Path
from typing import Dict, Optional


logger = logging.getLogger(__name__)


class RepositoryManager:
    """Utility for cloning and updating external repositories."""

    def __init__(self, base_dir: Optional[Path] = None):
        project_root = Path(__file__).resolve().parents[2]
        self.base_dir = Path(base_dir) if base_dir else project_root / "data" / "repositories"
        self.base_dir.mkdir(parents=True, exist_ok=True)

    def ensure_repository(self, name: str, repo_info: Dict[str, str]) -> Path:
        """Ensure repository exists locally and is checked out to requested revision."""
        repo_path = self.base_dir / name
        if not repo_path.exists():
            self._clone_repository(repo_path, repo_info.get("url"))
        else:
            self._fetch_repository(repo_path)
        self._checkout_revision(repo_path, repo_info)
        return repo_path

    def _clone_repository(self, repo_path: Path, url: Optional[str]) -> None:
        if not url:
            raise ValueError("Repository URL is required for cloning.")
        logger.info("Cloning repository %s into %s", url, repo_path)
        self._run_git(["clone", url, str(repo_path)])

    def _fetch_repository(self, repo_path: Path) -> None:
        logger.info("Fetching updates for repository at %s", repo_path)
        self._run_git(["fetch", "--all", "--tags"], cwd=repo_path)

    def _checkout_revision(self, repo_path: Path, repo_info: Dict[str, str]) -> None:
        target = (
            repo_info.get("commit")
            or repo_info.get("version")
            or repo_info.get("branch")
            or "main"
        )
        logger.info("Checking out %s in %s", target, repo_path)
        self._run_git(["checkout", target], cwd=repo_path)

        if repo_info.get("commit"):
            self._run_git(["reset", "--hard", repo_info["commit"]], cwd=repo_path)
        elif repo_info.get("version"):
            self._run_git(["reset", "--hard", repo_info["version"]], cwd=repo_path)
        else:
            self._run_git(["pull", "--ff-only"], cwd=repo_path)

    @staticmethod
    def _run_git(args, cwd: Optional[Path] = None) -> None:
        subprocess.run(["git", *args], cwd=cwd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
