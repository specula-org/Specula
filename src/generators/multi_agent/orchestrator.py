"""Main orchestrator for multi-agent TLA+ generation workflow"""

import logging
import json
from pathlib import Path
from typing import Optional

from .agents import (
    ArchitectureAnalyzer,
    SkeletonGenerator,
    SubsystemTranslator,
    SpecIntegrator,
    ConsistencyValidator
)

logger = logging.getLogger(__name__)


class MultiAgentOrchestrator:
    """
    Orchestrates the multi-agent workflow:
    1. ArchitectureAnalyzer: Analyze code structure and design data
    2. SkeletonGenerator: Generate TLA+ skeleton
    3. SubsystemTranslator: Translate each subsystem (can be parallel)
    4. SpecIntegrator: Integrate all subsystems
    5. ConsistencyValidator: Validate final spec
    """

    def __init__(self, llm_client, prompts_dir: Optional[Path] = None):
        self.llm = llm_client
        self.prompts_dir = prompts_dir or Path("src/prompts/multi_agent")

        # Initialize all agents
        self.architecture_analyzer = ArchitectureAnalyzer(self.llm, self.prompts_dir / "architecture_analyzer")
        self.skeleton_generator = SkeletonGenerator(self.llm, self.prompts_dir / "skeleton_generator")
        self.subsystem_translator = SubsystemTranslator(self.llm, self.prompts_dir / "subsystem_translator")
        self.spec_integrator = SpecIntegrator(self.llm, self.prompts_dir / "spec_integrator")
        self.consistency_validator = ConsistencyValidator(self.llm, self.prompts_dir / "consistency_validator")

    def generate(self,
                 source_code: str,
                 output_dir: Path) -> str:
        """
        Run the complete multi-agent pipeline

        Args:
            source_code: Source code to translate
            output_dir: Directory to save intermediate outputs

        Returns:
            Final TLA+ specification
        """
        logger.info("=" * 60)
        logger.info("Multi-Agent TLA+ Generation Pipeline")
        logger.info("=" * 60)

        output_dir.mkdir(parents=True, exist_ok=True)

        # Stage 1: Architecture Analysis
        logger.info("\n[Stage 1/5] Architecture Analysis")
        architecture = self.architecture_analyzer.run(source_code)
        self._save_checkpoint(output_dir / "1_architecture.json", architecture)
        logger.info(f"  → Identified {len(architecture.subsystems)} subsystems")

        # Stage 2: Skeleton Generation
        logger.info("\n[Stage 2/5] Skeleton Generation")
        skeleton = self.skeleton_generator.run(architecture)
        self._save_checkpoint(output_dir / "2_skeleton.tla", skeleton.spec_content)
        logger.info(f"  → Generated skeleton with {len(skeleton.stub_actions)} stub actions")

        # Stage 3: Subsystem Translation
        logger.info("\n[Stage 3/5] Subsystem Translation")
        subsystem_impls = self.subsystem_translator.run_parallel(
            architecture.subsystems,
            skeleton,
            source_code
        )
        for i, impl in enumerate(subsystem_impls):
            self._save_checkpoint(
                output_dir / f"3_subsystem_{impl.subsystem_name}.json",
                impl
            )
        logger.info(f"  → Translated {len(subsystem_impls)} subsystems")

        # Stage 4: Integration
        logger.info("\n[Stage 4/5] Spec Integration")
        integrated_spec = self.spec_integrator.run(skeleton, subsystem_impls)
        self._save_checkpoint(output_dir / "4_integrated.tla", integrated_spec)
        logger.info("  → Integrated all subsystems")

        # Stage 5: Validation
        logger.info("\n[Stage 5/5] Consistency Validation")
        final_spec = self.consistency_validator.run(integrated_spec, source_code)
        self._save_checkpoint(output_dir / "5_final.tla", final_spec)
        logger.info("  → Validation complete")

        logger.info("\n" + "=" * 60)
        logger.info("Multi-Agent Pipeline Complete")
        logger.info(f"Final spec saved to: {output_dir / '5_final.tla'}")
        logger.info("=" * 60)

        return final_spec

    def _save_checkpoint(self, path: Path, data):
        """Save checkpoint data (handles both strings and objects)"""
        if isinstance(data, str):
            path.write_text(data)
        else:
            # For dataclass objects, save as JSON
            with open(path, 'w') as f:
                if hasattr(data, '__dict__'):
                    json.dump(data.__dict__, f, indent=2, default=str)
                else:
                    json.dump(data, f, indent=2, default=str)
        logger.debug(f"Saved checkpoint: {path}")
