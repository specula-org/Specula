"""Breakpoint data structures and statistics."""

from dataclasses import dataclass, field
from typing import List, Optional


@dataclass
class Breakpoint:
    """Represents a source breakpoint.

    Attributes:
        line: Line number for the breakpoint
        file: Source file name (None = use default spec file)
        condition: Optional TLA+ expression to conditionally break
        description: Human-readable description for reporting
    """
    line: int
    file: Optional[str] = None
    condition: Optional[str] = None
    description: str = ""


@dataclass
class BreakpointHit:
    """Statistics for a single breakpoint.

    Attributes:
        file: Source file name
        line: Line number
        description: Breakpoint description
        hit_count: Number of times this breakpoint was hit
    """
    file: str
    line: int
    description: str
    hit_count: int = 0


@dataclass
class BreakpointStatistics:
    """Collected statistics from a debugging session.

    Attributes:
        hits: List of breakpoint hit statistics
        total_hits: Total number of breakpoint hits across all breakpoints
    """
    hits: List[BreakpointHit] = field(default_factory=list)
    total_hits: int = 0

    def get_hit_count(self, line: int, file: Optional[str] = None) -> int:
        """Get hit count for a specific breakpoint.

        Args:
            line: Line number
            file: File name (None matches any file)

        Returns:
            Number of times this breakpoint was hit
        """
        for hit in self.hits:
            if hit.line == line and (file is None or hit.file == file):
                return hit.hit_count
        return 0

    def get_never_hit(self) -> List[BreakpointHit]:
        """Get breakpoints that were never hit.

        Returns:
            List of breakpoints with hit_count == 0
        """
        return [hit for hit in self.hits if hit.hit_count == 0]

    def get_hit_breakpoints(self) -> List[BreakpointHit]:
        """Get breakpoints that were hit at least once.

        Returns:
            List of breakpoints with hit_count > 0
        """
        return [hit for hit in self.hits if hit.hit_count > 0]

    def print_summary(self, show_all: bool = True):
        """Print statistics summary with visual indicators.

        Args:
            show_all: If True, show all breakpoints. If False, only show hit breakpoints.
        """
        print(f"\n{'='*70}")
        print(f"Breakpoint Statistics Summary")
        print(f"{'='*70}")
        print(f"Total hits: {self.total_hits}")
        print(f"Breakpoints hit: {len(self.get_hit_breakpoints())}/{len(self.hits)}")
        print(f"\nDetailed breakdown:")

        for hit in self.hits:
            if not show_all and hit.hit_count == 0:
                continue

            status = "✅" if hit.hit_count > 0 else "❌"
            file_display = hit.file if hit.file else "(default)"
            print(f"  {status} {file_display:30s} Line {hit.line:3d}: "
                  f"{hit.hit_count:3d} hits - {hit.description}")

        # Summary of never-hit breakpoints
        never_hit = self.get_never_hit()
        if never_hit:
            print(f"\n💡 {len(never_hit)} breakpoint(s) were never hit:")
            for hit in never_hit:
                file_display = hit.file if hit.file else "(default)"
                print(f"     {file_display}:{hit.line} - {hit.description}")
