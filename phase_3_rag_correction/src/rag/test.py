import sys
import os
from basic_retriever import ErrorRetriever

def test_error_retrieval(query: str):
    """测试错误检索功能
    
    Args:
        query: 查询的错误信息
    """
    # 初始化检索器
    data_path = "/home/ubuntu/LLM_gen/spec_rag_system/knowledge_base/raw_errors/sany_errors/initial_errors.json"
    retriever = ErrorRetriever(data_path)
    
    # 执行检索
    results = retriever.search(query, top_k=3)
    
    # 打印结果
    print(results)

if __name__ == "__main__":
    # 测试用例
    test_cases = [
        "Encountered \"/\" at line 12, column 8 and token \")\" "
    ]
    
    for query in test_cases:
        test_error_retrieval(query)
        print("\n" + "="*80 + "\n")
