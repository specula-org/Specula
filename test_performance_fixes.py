#!/usr/bin/env python3
"""
Test script to verify performance fixes in Specula
"""

import sys
from pathlib import Path


def test_llm_cache_creation():
    """Test that LLM cache directory is created properly"""
    print("Testing LLM cache creation...")

    try:
        # Import cache class
        sys.path.insert(0, str(Path(__file__).parent / "src"))
        from llm.client import LLMCache

        # Create cache instance
        cache = LLMCache()

        # Check if cache directory exists
        if cache.cache_dir.exists():
            print("✅ LLM cache directory created successfully")
            return True
        else:
            print("❌ LLM cache directory not created")
            return False
    except Exception as e:
        print(f"❌ LLM cache creation failed: {e}")
        return False


def test_cache_key_generation():
    """Test that cache keys are generated deterministically"""
    print("Testing cache key generation...")

    try:
        from llm.client import LLMCache

        cache = LLMCache()

        # Generate keys for same content
        key1 = cache._get_cache_key("prompt1", "content1", "model1", 0.1, 1000)
        key2 = cache._get_cache_key("prompt1", "content1", "model1", 0.1, 1000)

        # Generate key for different content
        key3 = cache._get_cache_key("prompt2", "content2", "model1", 0.1, 1000)

        if key1 == key2 and key1 != key3:
            print("✅ Cache key generation working correctly")
            return True
        else:
            print("❌ Cache key generation failed")
            return False
    except Exception as e:
        print(f"❌ Cache key generation failed: {e}")
        return False


def test_cache_operations():
    """Test cache set/get operations"""
    print("Testing cache operations...")

    try:
        from llm.client import LLMCache

        cache = LLMCache()

        # Test data
        test_data = {
            "prompt": "test_prompt",
            "content": "test_content",
            "model": "test_model",
            "temperature": 0.1,
            "max_tokens": 1000,
            "response": "test_response",
        }

        # Set cache
        cache.set(**test_data)

        # Get cache
        cached_response = cache.get(
            test_data["prompt"],
            test_data["content"],
            test_data["model"],
            test_data["temperature"],
            test_data["max_tokens"],
        )

        if cached_response == test_data["response"]:
            print("✅ Cache operations working correctly")
            return True
        else:
            print("❌ Cache operations failed")
            return False
    except Exception as e:
        print(f"❌ Cache operations failed: {e}")
        return False


def test_cache_stats():
    """Test cache statistics functionality"""
    print("Testing cache statistics...")

    try:
        from llm.client import LLMCache

        cache = LLMCache()

        # Get stats
        stats = cache.get_stats()

        if isinstance(stats, dict) and "cache_files" in stats:
            print("✅ Cache statistics working correctly")
            return True
        else:
            print("❌ Cache statistics failed")
            return False
    except Exception as e:
        print(f"❌ Cache statistics failed: {e}")
        return False


def test_cache_clear():
    """Test cache clearing functionality"""
    print("Testing cache clearing...")

    try:
        from llm.client import LLMCache

        cache = LLMCache()

        # Clear cache
        cache.clear()

        # Check stats after clearing
        stats = cache.get_stats()

        if stats.get("cache_files", 0) == 0:
            print("✅ Cache clearing working correctly")
            return True
        else:
            print("❌ Cache clearing failed")
            return False
    except Exception as e:
        print(f"❌ Cache clearing failed: {e}")
        return False


def main():
    """Run all performance tests"""
    print("🚀 Running Specula Performance Fix Verification Tests")
    print("=" * 50)

    tests = [
        test_llm_cache_creation,
        test_cache_key_generation,
        test_cache_operations,
        test_cache_stats,
        test_cache_clear,
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
        print("🎉 All performance tests passed!")
        return 0
    else:
        print("⚠️  Some performance tests failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
