import torch
from sentence_transformers import SentenceTransformer
import json
import numpy as np
from typing import List, Dict

class ErrorRetriever:
    def __init__(self, data_path: str):
        """初始化检索器
        
        Args:
            data_path: 错误数据文件路径
        """
        # 加载预训练模型
        model_path = '/home/ubuntu/.cache/huggingface/huball-MiniLM-L6-v2'  # 本地模型路径
        try:
            self.model = SentenceTransformer(
                model_path,
                device="cpu",
                local_files_only=True,  # 强制使用本地文件
            )
            print(f"成功加载模型: {model_path}")
        except Exception as e:
            print(f"模型加载失败，请检查路径是否正确: {str(e)}")
            raise
        
        # 加载错误数据
        with open(data_path, 'r', encoding='utf-8') as f:
            self.error_data = json.load(f)
            
        # 对错误信息进行编码
        self.error_embeddings = self._encode_errors()
        
    def _encode_errors(self) -> torch.Tensor:
        """将所有错误信息编码为向量"""
        error_texts = [err['error_message'] for err in self.error_data]
        print(f"准备编码 {len(error_texts)} 条错误信息")
        return self.model.encode(
            error_texts,
            normalize_embeddings=True,
            convert_to_tensor=True,
            batch_size=32
        )
    
    def search(self, query: str, top_k: int = 3) -> List[Dict]:
        """检索最相似的错误
        
        Args:
            query: 查询文本
            top_k: 返回结果数量
            
        Returns:
            最相似的top_k个错误信息
        """
        print(f"\n开始搜索，查询文本: {query}")
        
        # 对查询文本编码
        print("正在对查询文本进行编码...")
        query_embedding = self.model.encode(
            query,
            normalize_embeddings=True,
            convert_to_tensor=True
        )
        print("查询文本编码完成")
        
        # 计算余弦相似度
        print("计算余弦相似度...")
        cos_scores = torch.nn.functional.cosine_similarity(
            query_embedding.unsqueeze(0), 
            self.error_embeddings, 
            dim=1
        )
        print("余弦相似度计算完成")
        
        # 获取top_k结果索引
        top_indices = torch.argsort(cos_scores, descending=True)[:top_k]
        
        # 返回结果
        results = []
        for idx in top_indices:
            error = self.error_data[idx]
            error['similarity_score'] = float(cos_scores[idx])
            results.append(error)
            
        print(f"检索完成，找到 {len(results)} 条相关结果")
        return results
