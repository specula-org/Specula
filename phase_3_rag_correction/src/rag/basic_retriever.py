import torch
from sentence_transformers import SentenceTransformer
import json
import numpy as np
from typing import List, Dict

class ErrorRetriever:
    def __init__(self, data_path: str):
        """Initialize retriever
        
        Args:
            data_path: Error data file path
        """
        # Load pre-trained model
        model_path = '/home/ubuntu/.cache/huggingface/huball-MiniLM-L6-v2'  # Local model path
        try:
            self.model = SentenceTransformer(
                model_path,
                device="cpu",
                local_files_only=True,  # Force use of local files
            )
            print(f"Successfully loaded model: {model_path}")
        except Exception as e:
            print(f"Model loading failed, please check if path is correct: {str(e)}")
            raise
        
        # Load error data
        with open(data_path, 'r', encoding='utf-8') as f:
            self.error_data = json.load(f)
            
        # Encode error information
        self.error_embeddings = self._encode_errors()
        
    def _encode_errors(self) -> torch.Tensor:
        """Encode all error information into vectors"""
        error_texts = [err['error_message'] for err in self.error_data]
        print(f"Preparing to encode {len(error_texts)} error messages")
        return self.model.encode(
            error_texts,
            normalize_embeddings=True,
            convert_to_tensor=True,
            batch_size=32
        )
    
    def search(self, query: str, top_k: int = 3) -> List[Dict]:
        """Retrieve most similar errors
        
        Args:
            query: Query text
            top_k: Number of results to return
            
        Returns:
            Top-k most similar error information
        """
        print(f"\nStarting search, query text: {query}")
        
        # Encode query text
        print("Encoding query text...")
        query_embedding = self.model.encode(
            query,
            normalize_embeddings=True,
            convert_to_tensor=True
        )
        print("Query text encoding completed")
        
        # Calculate cosine similarity
        print("Calculating cosine similarity...")
        cos_scores = torch.nn.functional.cosine_similarity(
            query_embedding.unsqueeze(0), 
            self.error_embeddings, 
            dim=1
        )
        print("Cosine similarity calculation completed")
        
        # Get top_k result indices
        top_indices = torch.argsort(cos_scores, descending=True)[:top_k]
        
        # Return results
        results = []
        for idx in top_indices:
            error = self.error_data[idx]
            error['similarity_score'] = float(cos_scores[idx])
            results.append(error)
            
        print(f"Search completed, found {len(results)} relevant results")
        return results
