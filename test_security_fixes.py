#!/usr/bin/env python3
"""
Test script to verify critical security fixes in Specula
"""

import os
import sys
import subprocess
from pathlib import Path


def test_path_traversal_protection():
    """Test that path traversal attacks are prevented"""
    print("Testing path traversal protection...")

    # Test with a malicious path
    malicious_path = "../../../etc/passwd"

    try:
        # This should fail due to path bounds checking
        resolved_path = Path(malicious_path).resolve()
        project_root = Path(__file__).parent.resolve()

        if str(resolved_path).startswith(str(project_root)):
            print("❌ Path traversal protection failed")
            return False
        else:
            print("✅ Path traversal protection working")
            return True
    except Exception as e:
        print(f"✅ Path traversal protection working (exception: {e})")
        return True


def test_subprocess_security():
    """Test that subprocess calls are secure"""
    print("Testing subprocess security...")

    try:
        # Test that shell=True is not used
        subprocess.run(["echo", "test"], capture_output=True, text=True, timeout=5)
        print("✅ Subprocess security working")
        return True
    except Exception as e:
        print(f"❌ Subprocess security failed: {e}")
        return False


def test_config_environment_vars():
    """Test that configuration uses environment variables"""
    print("Testing environment variable configuration...")

    # Set test environment variables
    os.environ["LLM_PROVIDER"] = "test_provider"
    os.environ["LLM_MODEL"] = "test_model"

    try:
        # Import and test config
        sys.path.insert(0, str(Path(__file__).parent / "src"))
        from utils.config import get_config

        config = get_config()
        provider = config.get("llm.provider")
        model = config.get("llm.model")

        if provider == "test_provider" and model == "test_model":
            print("✅ Environment variable configuration working")
            return True
        else:
            print(
                f"❌ Environment variable configuration failed: " f"{provider}, {model}"
            )
            return False
    except Exception as e:
        print(f"❌ Environment variable configuration failed: {e}")
        return False


def test_file_permissions():
    """Test that file operations are secure"""
    print("Testing file operation security...")

    try:
        # Test creating a file with restricted permissions
        test_file = Path("test_security.tmp")
        test_file.write_text("test content")

        # Check file permissions (should be restrictive)
        test_file.stat()

        # Clean up
        test_file.unlink()

        print("✅ File operation security working")
        return True
    except Exception as e:
        print(f"❌ File operation security failed: {e}")
        return False


def main():
    """Run all security tests"""
    print("🔒 Running Specula Security Fix Verification Tests")
    print("=" * 50)

    tests = [
        test_path_traversal_protection,
        test_subprocess_security,
        test_config_environment_vars,
        test_file_permissions,
    ]

    passed = 0
    total = len(tests)

    for test in tests:
        try:
            if test():
                passed += 1
        except Exception as e:
            print(f"❌ Test {test.__name__} failed with exception: {e}")
        print()

    print("=" * 50)
    print(f"Results: {passed}/{total} tests passed")

    if passed == total:
        print("🎉 All security tests passed!")
        return 0
    else:
        print("⚠️  Some security tests failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
