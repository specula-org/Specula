"""Autosave utilities for Specula CLI runs."""

import json
import logging
import os
import hashlib
import shutil
from datetime import datetime
from pathlib import Path
from typing import Dict, Optional, Tuple

import yaml


class AutosaveManager:
    """Manage autosave artifacts, prompts, logs, and metadata for generation runs."""

    def __init__(self, base_dir: Path, enabled: bool = False, config_path: Optional[str] = None):
        self.enabled = enabled
        self.base_dir = Path(base_dir)
        self.config_path = Path(config_path) if config_path else None
        self.session_dir: Optional[Path] = None
        self.log_handler: Optional[logging.Handler] = None
        self.metadata: Dict = {}
        self.prompt_counter = 0
        self._prompt_entries: Dict[str, Dict] = {}
        self.log_file: Optional[Path] = None
        self.versions_dir = self.base_dir / "versions"
        self.config_versions_dir = self.versions_dir / "configs"

    # -----------------------------
    # Session lifecycle
    # -----------------------------
    def start_session(self, input_path: str, output_dir: str):
        if not self.enabled:
            return

        # Reset session-scoped state so runs start fresh even if manager is reused.
        self.prompt_counter = 0
        self._prompt_entries.clear()
        timestamp = datetime.utcnow().strftime("%Y%m%d-%H%M%S")
        input_stem = Path(input_path).stem or "input"
        session_name = f"{timestamp}_{self._sanitize_name(input_stem)}"
        self.base_dir.mkdir(parents=True, exist_ok=True)
        self.versions_dir.mkdir(parents=True, exist_ok=True)
        self.config_versions_dir.mkdir(parents=True, exist_ok=True)

        session_dir = self.base_dir / session_name
        counter = 1
        while session_dir.exists():
            session_dir = self.base_dir / f"{session_name}_{counter}"
            counter += 1

        session_dir.mkdir(parents=True, exist_ok=True)
        self.session_dir = session_dir

        logs_dir = self.session_dir / "logs"
        logs_dir.mkdir(parents=True, exist_ok=True)
        self.log_file = logs_dir / "run.log"
        self.log_handler = logging.FileHandler(self.log_file, encoding='utf-8')
        self.log_handler.setLevel(logging.NOTSET)
        self.log_handler.setFormatter(logging.Formatter('[%(levelname)s] %(message)s'))
        logging.getLogger().addHandler(self.log_handler)

        self.metadata = {
            "timestamp": timestamp,
            "input_file": str(input_path),
            "output_dir": str(output_dir),
            "session_dir": str(self.session_dir),
            "log_file": str(self._relative_to_session(self.log_file))
        }
        self.metadata.setdefault("prompts", [])
        self.metadata.setdefault("artifacts", [])

    def finalize(self, summary: Optional[Dict] = None, exit_code: int = 0, error: Optional[str] = None):
        if not self.enabled or not self.session_dir:
            return

        try:
            if summary is not None:
                self.metadata["summary"] = summary
            if error:
                self.metadata.setdefault("errors", []).append(str(error))
            self.metadata["exit_code"] = exit_code
            self.metadata["status"] = "success" if exit_code == 0 else "error"

            metadata_path = self.session_dir / "metadata.json"
            with open(metadata_path, 'w', encoding='utf-8') as f:
                json.dump(self.metadata, f, indent=2, ensure_ascii=False)
        finally:
            if self.log_handler:
                logging.getLogger().removeHandler(self.log_handler)
                self.log_handler.close()

    # -----------------------------
    # Recording helpers
    # -----------------------------
    def snapshot_config(self, config_data: Dict, label: str = "base", source_path: Optional[str] = None):
        if not self.enabled or not self.session_dir:
            return

        effective_source = source_path if source_path is not None else (str(self.config_path) if self.config_path else None)

        if effective_source and self.config_path and Path(effective_source) == self.config_path and self.config_path.exists():
            config_bytes = self.config_path.read_bytes()
            suffix = self.config_path.suffix or ".yaml"
        else:
            config_bytes = yaml.dump(config_data, sort_keys=False).encode('utf-8')
            suffix = ".yaml"

        config_hash, stored_path = self._store_versioned_file(config_bytes, suffix, self.config_versions_dir)

        session_config_dir = self.session_dir / "config"
        session_config_dir.mkdir(exist_ok=True)
        session_config_name = f"config_{self._sanitize_name(label)}_{config_hash[:8]}{suffix}"
        session_config_path = session_config_dir / session_config_name
        self._link_or_copy(stored_path, session_config_path)

        entry = {
            "label": label,
            "hash": config_hash,
            "path": str(self._relative_to_session(session_config_path))
        }
        self.metadata.setdefault("configs", []).append(entry)

    def record_override(self, key: str, value):
        if not self.enabled or value is None:
            return
        overrides = self.metadata.setdefault("overrides", {})
        overrides[key] = value

    def record_prompt(self, name: str, prompt_content: str) -> Optional[str]:
        if not self.enabled or not self.session_dir:
            return None

        self.prompt_counter += 1
        order = self.prompt_counter
        entry_id = f"prompt_{order:03d}"

        prompts_dir = self.session_dir / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        prompt_filename = f"{order:03d}_{self._sanitize_name(name)}.txt"
        prompt_path = prompts_dir / prompt_filename
        prompt_path.write_text(prompt_content, encoding='utf-8')
        prompt_hash = hashlib.sha256(prompt_content.encode('utf-8')).hexdigest()

        entry = {
            "id": entry_id,
            "order": order,
            "name": name,
            "prompt_hash": prompt_hash,
            "prompt_path": str(self._relative_to_session(prompt_path))
        }
        self.metadata.setdefault("prompts", []).append(entry)
        self._prompt_entries[entry_id] = entry
        return entry_id

    def record_response(self, entry_id: Optional[str], response_text: str, suffix: str = "response"):
        if not self.enabled or not self.session_dir or not entry_id:
            return

        entry = self._prompt_entries.get(entry_id)
        if not entry:
            return

        responses_dir = self.session_dir / "responses"
        responses_dir.mkdir(exist_ok=True)
        filename = f"{entry['order']:03d}_{self._sanitize_name(entry['name'])}_{self._sanitize_name(suffix)}.txt"
        response_path = responses_dir / filename
        response_path.write_text(response_text, encoding='utf-8')
        entry.setdefault("responses", [])
        entry["responses"].append(str(self._relative_to_session(response_path)))

    def record_artifact(self, name: str, source_path: Path):
        if not self.enabled or not self.session_dir:
            return

        artifact_source = Path(source_path)
        if not artifact_source.exists():
            return

        artifacts_dir = self.session_dir / "artifacts"
        artifacts_dir.mkdir(exist_ok=True)

        index = len(self.metadata.get("artifacts", [])) + 1
        artifact_filename = f"{index:03d}_{self._sanitize_name(name)}_{artifact_source.name}"
        target_path = artifacts_dir / artifact_filename
        shutil.copy2(artifact_source, target_path)

        self.metadata.setdefault("artifacts", []).append({
            "name": name,
            "path": str(self._relative_to_session(target_path))
        })

    def set_summary(self, summary: Dict):
        if not self.enabled:
            return
        self.metadata["summary"] = summary

    # -----------------------------
    # Internal helpers
    # -----------------------------
    def _store_versioned_file(self, content: bytes, suffix: str, versions_dir: Path) -> Tuple[str, Path]:
        digest = hashlib.sha256(content).hexdigest()
        versions_dir.mkdir(parents=True, exist_ok=True)
        version_path = versions_dir / f"{digest}{suffix}"
        if not version_path.exists():
            version_path.write_bytes(content)
        return digest, version_path

    def _link_or_copy(self, src: Path, dest: Path):
        if dest.exists():
            return
        dest.parent.mkdir(parents=True, exist_ok=True)
        try:
            relative_src = os.path.relpath(src, dest.parent)
            os.symlink(relative_src, dest)
        except OSError:
            shutil.copy2(src, dest)

    def _sanitize_name(self, name: str) -> str:
        sanitized = ''.join(c if c.isalnum() or c in ('-', '_') else '_' for c in name)
        sanitized = sanitized.strip('_') or "item"
        return sanitized[:80]

    def _relative_to_session(self, path: Path) -> str:
        try:
            return os.path.relpath(path, self.session_dir)
        except Exception:
            return str(path)


__all__ = ["AutosaveManager"]
