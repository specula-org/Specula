#!/usr/bin/env python3
"""
Simple test script for TLA+ RAG Error Correction System
"""

import os
import sys
import subprocess
from pathlib import Path

def test_environment_check():
    """Test environment check functionality"""
    print("🧪 Testing environment check...")
    result = subprocess.run([sys.executable, "main.py", "--check-env"], 
                          capture_output=True, text=True)
    
    if "Checking environment configuration..." in result.stdout:
        print("✅ Environment check function works")
        return True
    else:
        print("❌ Environment check function failed")
        print(f"Output: {result.stdout}")
        print(f"Error: {result.stderr}")
        return False

def test_help():
    """Test help functionality"""
    print("🧪 Testing help functionality...")
    result = subprocess.run([sys.executable, "main.py", "--help"], 
                          capture_output=True, text=True)
    
    if "TLA+ RAG Error Correction System" in result.stdout:
        print("✅ Help function works")
        return True
    else:
        print("❌ Help function failed")
        return False

def test_input_validation():
    """Test input validation"""
    print("🧪 Testing input validation...")
    
    # Test with missing arguments
    result = subprocess.run([sys.executable, "main.py", "--input", "nonexistent.yaml"], 
                          capture_output=True, text=True)
    
    if "required when not using --check-env" in result.stdout:
        print("✅ Input validation works")
        return True
    else:
        print("❌ Input validation failed")
        return False

def test_file_structure():
    """Test if all required files exist"""
    print("🧪 Testing file structure...")
    
    required_files = [
        "main.py",
        "config.yaml", 
        "setup.sh",
        "requirements.txt",
        "example_input.yaml",
        "README.md",
        "src/config.py",
        "src/llm_client.py", 
        "src/processor.py",
        "src/rag/basic_retriever.py",
        "src/processing/get_errors.py"
    ]
    
    missing_files = []
    for file_path in required_files:
        if not Path(file_path).exists():
            missing_files.append(file_path)
    
    if not missing_files:
        print("✅ All required files exist")
        return True
    else:
        print(f"❌ Missing files: {missing_files}")
        return False

def main():
    """Run all tests"""
    print("🚀 Starting TLA+ RAG Error Correction System Tests\n")
    
    tests = [
        test_file_structure,
        test_help,
        test_environment_check,
        test_input_validation
    ]
    
    passed = 0
    total = len(tests)
    
    for test in tests:
        try:
            if test():
                passed += 1
            print()  # Add spacing between tests
        except Exception as e:
            print(f"❌ Test failed with exception: {e}\n")
    
    print(f"📊 Test Results: {passed}/{total} tests passed")
    
    if passed == total:
        print("🎉 All tests passed! The system is ready to use.")
        return 0
    else:
        print("⚠️  Some tests failed. Please check the issues above.")
        return 1

if __name__ == "__main__":
    sys.exit(main()) 