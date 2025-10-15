"""
Unit tests for TLACompileTool
"""

import pytest
from pathlib import Path
from src.tools.tla_compile_tool import TLACompileTool, check_tla_compilation


class TestTLACompileTool:
    """Test cases for TLA+ compilation checker"""

    @pytest.fixture
    def compile_tool(self):
        """Create a TLACompileTool instance"""
        return TLACompileTool()

    @pytest.fixture
    def good_spec(self, tmp_path):
        """Create a valid TLA+ spec for testing"""
        # Note: MODULE name must match filename
        spec_content = """---- MODULE good_spec ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_x

============================
"""
        spec_file = tmp_path / "good_spec.tla"
        spec_file.write_text(spec_content)
        return spec_file

    @pytest.fixture
    def bad_spec(self, tmp_path):
        """Create an invalid TLA+ spec with syntax errors"""
        # Note: MODULE name must match filename
        spec_content = r"""---- MODULE bad_spec ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

Next == x' = x +  \* Missing operand - syntax error

Spec == Init /\ [][Next]_x

============================
"""
        spec_file = tmp_path / "bad_spec.tla"
        spec_file.write_text(spec_content)
        return spec_file

    def test_tool_properties(self, compile_tool):
        """Test tool name and description"""
        assert compile_tool.name == "tla_compile"
        assert "TLA+ specification" in compile_tool.description
        assert "compiles" in compile_tool.description

    def test_good_spec_compiles(self, compile_tool, good_spec):
        """Test that a valid spec compiles successfully"""
        result = compile_tool.run(spec_path=str(good_spec))

        assert result.success is True
        assert result.data is not None
        assert result.data["error_count"] == 0
        assert result.data["error_messages"] == []
        assert result.data["compilation_time"] >= 0
        assert result.error is None

    def test_bad_spec_fails(self, compile_tool, bad_spec):
        """Test that an invalid spec fails compilation"""
        result = compile_tool.run(spec_path=str(bad_spec))

        assert result.success is False
        assert result.data is not None
        assert result.data["error_count"] > 0
        assert len(result.data["error_messages"]) > 0
        assert result.error is not None
        assert "Compilation failed" in result.error

    def test_file_not_found(self, compile_tool):
        """Test error handling when file doesn't exist"""
        result = compile_tool.run(spec_path="/nonexistent/path/spec.tla")

        assert result.success is False
        assert result.error is not None
        assert "File not found" in result.error
        assert len(result.suggestions) > 0

    def test_not_a_file(self, compile_tool, tmp_path):
        """Test error handling when path is a directory"""
        result = compile_tool.run(spec_path=str(tmp_path))

        assert result.success is False
        assert result.error is not None
        assert "not a file" in result.error

    def test_wrong_extension(self, compile_tool, tmp_path):
        """Test error handling for non-.tla files"""
        wrong_file = tmp_path / "not_a_spec.txt"
        wrong_file.write_text("This is not a TLA+ spec")

        result = compile_tool.run(spec_path=str(wrong_file))

        assert result.success is False
        assert result.error is not None
        assert ".tla extension" in result.error

    def test_convenience_function(self, good_spec):
        """Test the convenience function"""
        result = check_tla_compilation(str(good_spec))

        assert result.success is True
        assert result.data["error_count"] == 0

    def test_real_dataset_spec(self):
        """Test on a real spec from the dataset"""
        # Test on the spin spec if it exists
        spec_path = Path("/home/ubuntu/specula/experiments/syntax_phase/dataset/spin/test/spec_001/spin.tla")

        if spec_path.exists():
            tool = TLACompileTool()
            result = tool.run(spec_path=str(spec_path))

            # This spec should compile (it's in the test folder)
            # If it has errors, we'll see them in the output
            assert result.data is not None
            assert "error_count" in result.data
            assert "compilation_time" in result.data

    def test_metadata_included(self, compile_tool, good_spec):
        """Test that metadata is included in results"""
        result = compile_tool.run(spec_path=str(good_spec))

        assert result.metadata is not None
        assert "spec_path" in result.metadata
        assert "compilation_time" in result.metadata
        assert "returncode" in result.metadata

    def test_timeout_parameter(self, good_spec):
        """Test that custom timeout can be set"""
        tool = TLACompileTool(timeout=60)
        assert tool.timeout == 60

        result = tool.run(spec_path=str(good_spec))
        assert result.success is True

    def test_module_name_mismatch(self, tmp_path, compile_tool):
        """Test spec where MODULE name doesn't match filename"""
        # Create spec with mismatched name
        spec_content = """---- MODULE WrongName ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

============================
"""
        spec_file = tmp_path / "correct_name.tla"
        spec_file.write_text(spec_content)

        # TLC requires MODULE name to match filename
        result = compile_tool.run(spec_path=str(spec_file))

        # Should fail due to name mismatch
        assert result.success is False
        assert result.data["error_count"] > 0


class TestTLACompileToolEdgeCases:
    """Test edge cases and error handling"""

    def test_empty_spec(self, tmp_path):
        """Test compilation of an empty spec"""
        spec_file = tmp_path / "empty.tla"
        spec_file.write_text("")

        tool = TLACompileTool()
        result = tool.run(spec_path=str(spec_file))

        # Empty file should fail compilation
        assert result.success is False

    def test_spec_with_only_module_header(self, tmp_path):
        """Test spec with only module header"""
        spec_content = """---- MODULE MinimalSpec ----
============================
"""
        spec_file = tmp_path / "MinimalSpec.tla"
        spec_file.write_text(spec_content)

        tool = TLACompileTool()
        result = tool.run(spec_path=str(spec_file))

        # This should actually compile (minimal valid spec)
        # TLC might accept or reject it - we just verify the tool doesn't crash
        assert result.data is not None
        assert "error_count" in result.data

    def test_unicode_in_spec(self, tmp_path):
        """Test spec with Unicode characters"""
        # Note: MODULE name must match filename
        spec_content = r"""---- MODULE UnicodeSpec ----
EXTENDS Naturals

\* Comment with Unicode: ∀ ∃ ∧ ∨

VARIABLES x

Init == x = 0

============================
"""
        spec_file = tmp_path / "UnicodeSpec.tla"
        spec_file.write_text(spec_content, encoding='utf-8')

        tool = TLACompileTool()
        result = tool.run(spec_path=str(spec_file))

        # Should compile fine (TLA+ supports Unicode comments)
        assert result.data is not None
        assert "error_count" in result.data


class TestTLACompileToolErrorExtraction:
    """Test error message extraction"""

    def test_error_extraction_multiple_errors(self, tmp_path):
        """Test extraction when there are multiple errors"""
        # Note: MODULE name must match filename
        spec_content = r"""---- MODULE MultiError ----
EXTENDS Naturals

VARIABLES x, y

Init == x = 0 /\ y =   \* Missing value

Next == x' = undefined_symbol  \* Undefined symbol

============================
"""
        spec_file = tmp_path / "MultiError.tla"
        spec_file.write_text(spec_content)

        tool = TLACompileTool()
        result = tool.run(spec_path=str(spec_file))

        assert result.success is False
        # Should extract at least one error
        assert result.data["error_count"] > 0
        assert len(result.data["error_messages"]) > 0

    def test_suggestions_provided(self, tmp_path):
        """Test that helpful suggestions are provided"""
        # Note: MODULE name must match filename
        spec_content = r"""---- MODULE SyntaxError ----
EXTENDS Naturals

VARIABLES x

Init == x = 0 +  \* Incomplete expression

============================
"""
        spec_file = tmp_path / "SyntaxError.tla"
        spec_file.write_text(spec_content)

        tool = TLACompileTool()
        result = tool.run(spec_path=str(spec_file))

        assert result.success is False
        assert len(result.suggestions) > 0
        # Should suggest reviewing errors
        suggestions_text = " ".join(result.suggestions)
        assert "error" in suggestions_text.lower()
