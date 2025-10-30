import logging
import os
import shutil
import subprocess
from pathlib import Path
from typing import Optional

from src.core.instrumentation import InstrumentationTool
from src.utils.repository import RepositoryManager


logger = logging.getLogger(__name__)


REPOSITORY_INFO = {
    "url": "https://github.com/etcd-io/raft.git",
    "branch": "main",
    "version": "v3.5.12",
}


class EtcdTracePipeline:
    """End-to-end trace generation pipeline for etcd using the real raft library."""

    def __init__(
        self,
        config_path: Path,
        source_rel_path: str = "raft.go",
        workspace_dir: Optional[Path] = None,
        stub_template: Optional[Path] = None,
        helper_template: Optional[Path] = None,
        trace_output: Optional[Path] = None,
        base_repo_path: Optional[Path] = None,
        node_count: int = 3,
        duration_seconds: int = 60,
        client_qps: float = 10.0,
        fault_rate: float = 0.1,
        filter_type: str = "coarse",
    ):
        self.project_root = Path(__file__).resolve().parents[4]
        self.config_path = Path(config_path)
        self.source_rel_path = Path(source_rel_path)

        self.trace_gen_dir = (
            self.project_root
            / "src"
            / "systems"
            / "etcd"
            / "trace_generation"
            / "go"
        )
        self.templates_dir = (
            self.project_root / "src" / "systems" / "etcd" / "templates"
        )

        default_workspace = self.project_root / "output" / "etcd" / "raft_workspace"
        self.workspace_dir = Path(workspace_dir) if workspace_dir else default_workspace

        default_trace_output = (
            self.project_root / "output" / "etcd" / "traces" / "etcd_trace.ndjson"
        )
        self.trace_output = Path(trace_output) if trace_output else default_trace_output

        self.stub_template = (
            Path(stub_template)
            if stub_template
            else self.templates_dir / "go_trace_stub.template"
        )
        self.helper_template = (
            Path(helper_template)
            if helper_template
            else self.templates_dir / "trace_spec_action.go.template"
        )

        self.node_count = node_count
        self.duration_seconds = duration_seconds
        self.client_qps = client_qps
        self.fault_rate = fault_rate
        self.filter_type = filter_type

        env_repo = os.environ.get("SPECULA_ETCD_REPO_PATH")
        self._base_repo_override = (
            Path(base_repo_path)
            if base_repo_path
            else (Path(env_repo) if env_repo else None)
        )

        self._instrumentation_tool = InstrumentationTool()
        self._repo_manager = RepositoryManager()
        self.base_repo: Optional[Path] = None

    def run(self) -> Path:
        """Execute the full pipeline and return the generated trace path."""
        self._validate_paths()
        self._prepare_workspace()
        self._copy_helper_file()
        self._disable_builtin_tracing()
        self._patch_workspace_go_mod()
        self._instrument_source()
        self._update_trace_generator_go_mod()
        self._build_trace_generator()
        return self._run_trace_generator()

    def _validate_paths(self) -> None:
        if self._base_repo_override:
            if not self._base_repo_override.exists():
                raise FileNotFoundError(
                    f"Provided etcd repository path does not exist: {self._base_repo_override}"
                )
            self.base_repo = self._base_repo_override
        else:
            fallback_repo = (
                self.project_root.parent
                / "LLM_Gen_TLA_benchmark_framework"
                / "data"
                / "repositories"
                / "raft"
            )
            if fallback_repo.exists():
                self.base_repo = fallback_repo
            else:
                self.base_repo = self._repo_manager.ensure_repository("etcd", REPOSITORY_INFO)
        if not self.trace_gen_dir.exists():
            raise FileNotFoundError(f"Trace generator directory missing: {self.trace_gen_dir}")
        if not self.stub_template.exists():
            raise FileNotFoundError(f"Stub template not found: {self.stub_template}")
        if not self.helper_template.exists():
            raise FileNotFoundError(f"Helper template not found: {self.helper_template}")
        if not self.config_path.exists():
            raise FileNotFoundError(f"Instrumentation config not found: {self.config_path}")

    def _prepare_workspace(self) -> None:
        if self.base_repo is None:
            raise RuntimeError("Base repository not initialized.")
        if self.workspace_dir.exists():
            shutil.rmtree(self.workspace_dir)
        shutil.copytree(self.base_repo, self.workspace_dir)

    def _copy_helper_file(self) -> None:
        helper_dest = self.workspace_dir / "trace_spec_action.go"
        helper_dest.parent.mkdir(parents=True, exist_ok=True)
        helper_dest.write_text(self.helper_template.read_text())

    def _disable_builtin_tracing(self) -> None:
        state_trace_path = self.workspace_dir / "state_trace.go"
        if not state_trace_path.exists():
            return

        content = state_trace_path.read_text()
        original = (
            "func traceEvent(evt stateMachineEventType, r *raft, m *raftpb.Message, prop map[string]any) {\n"
            "\tif r.traceLogger == nil {\n"
            "\t\treturn\n"
            "\t}\n\n"
            "\tr.traceLogger.TraceEvent(&TracingEvent{\n"
            "\t\tName:       evt.String(),\n"
            "\t\tNodeID:     strconv.FormatUint(r.id, 10),\n"
            "\t\tState:      makeTracingState(r),\n"
            "\t\tLogSize:    r.raftLog.lastIndex(),\n"
            "\t\tConf:       [2][]string{formatConf(r.trk.Voters[0].Slice()), formatConf(r.trk.Voters[1].Slice())},\n"
            "\t\tRole:       r.state.String(),\n"
            "\t\tMessage:    makeTracingMessage(m),\n"
            "\t\tProperties: prop,\n"
            "\t})\n"
            "}\n"
        )

        replacement = (
            "func traceEvent(evt stateMachineEventType, r *raft, m *raftpb.Message, prop map[string]any) {\n"
            "\t// Disable etcd's built-in tracing to avoid polluting Specula traces.\n"
            "\treturn\n"
            "}\n"
        )

        if original not in content:
            logger.warning("Could not locate original traceEvent implementation; skipping disable step")
            return

        state_trace_path.write_text(content.replace(original, replacement, 1))

    def _patch_workspace_go_mod(self) -> None:
        go_mod_path = self.workspace_dir / "go.mod"
        if not go_mod_path.exists():
            return

        lines = []
        for line in go_mod_path.read_text().splitlines():
            stripped = line.strip()
            if stripped.startswith("toolchain "):
                continue
            if stripped.startswith("go "):
                lines.append("go 1.23")
            else:
                lines.append(line)
        go_mod_path.write_text("\n".join(lines) + "\n")

    def _instrument_source(self) -> None:
        config = self._instrumentation_tool.load_config(str(self.config_path))
        stub_template = self.stub_template.read_text().strip()

        source_path = self.workspace_dir / self.source_rel_path
        if not source_path.exists():
            raise FileNotFoundError(f"Source file for instrumentation not found: {source_path}")

        temp_output = source_path.with_suffix(source_path.suffix + ".instrumented")
        result = self._instrumentation_tool.instrument_source(
            config=config,
            source_file=str(source_path),
            stub_template=stub_template,
            output_file=str(temp_output),
            language="go",
        )
        logger.info(
            "Instrumentation complete: %s instrumented, %s skipped",
            result["instrumented_actions"],
            result["skipped_actions"],
        )
        source_path.write_text(temp_output.read_text())
        temp_output.unlink(missing_ok=True)

    def _update_trace_generator_go_mod(self) -> None:
        go_mod_path = self.trace_gen_dir / "go.mod"
        if not go_mod_path.exists():
            raise FileNotFoundError(f"go.mod not found: {go_mod_path}")

        relative_path = Path(os.path.relpath(self.workspace_dir, self.trace_gen_dir))
        lines = go_mod_path.read_text().splitlines()
        updated_lines = []
        found_replace = False

        for line in lines:
            stripped = line.strip()
            if stripped.startswith("replace go.etcd.io/raft/v3 =>"):
                updated_lines.append(f"replace go.etcd.io/raft/v3 => {relative_path}")
                found_replace = True
            elif stripped.startswith("toolchain "):
                continue
            elif stripped.startswith("go "):
                updated_lines.append("go 1.23")
            else:
                updated_lines.append(line)

        if not found_replace:
            updated_lines.append(f"replace go.etcd.io/raft/v3 => {relative_path}")

        go_mod_path.write_text("\n".join(updated_lines) + "\n")

    def _build_trace_generator(self) -> None:
        go_cache = self.project_root / "output" / "etcd" / "go_cache"
        go_mod_cache = Path(
            os.environ.get("GOMODCACHE", Path.home() / "go" / "pkg" / "mod")
        )
        go_cache.mkdir(parents=True, exist_ok=True)
        if not go_mod_cache.exists():
            go_mod_cache.mkdir(parents=True, exist_ok=True)

        env = os.environ.copy()
        env.update(
            {
                "GOCACHE": str(go_cache),
                "GOMODCACHE": str(go_mod_cache),
                "GOTOOLCHAIN": "local",
                "GOPROXY": "off",
                "GOSUMDB": "off",
            }
        )

        subprocess.run(
            ["go", "mod", "tidy"],
            cwd=self.trace_gen_dir,
            check=True,
            env=env,
        )
        subprocess.run(
            [
                "go",
                "build",
                "-tags",
                "with_tla",
                "-o",
                str(self.trace_gen_dir / "trace_generator"),
                "./cmd",
            ],
            cwd=self.trace_gen_dir,
            check=True,
            env=env,
        )

    def _run_trace_generator(self) -> Path:
        self.trace_output.parent.mkdir(parents=True, exist_ok=True)
        cmd = [
            str(self.trace_gen_dir / "trace_generator"),
            "-nodes",
            str(self.node_count),
            "-duration",
            str(self.duration_seconds),
            "-qps",
            str(self.client_qps),
            "-fault-rate",
            str(self.fault_rate),
            "-filter",
            self.filter_type,
            "-output",
            str(self.trace_output),
        ]
        subprocess.run(cmd, cwd=self.trace_gen_dir, check=True)
        return self.trace_output
