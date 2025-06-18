#!/usr/bin/env python3
"""
Phase 1: TLA+ Specification Generator
A two-step process: Code Translation + Error Correction
"""

import os
import sys
import json
import yaml
import argparse
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import logging

class Config:
    """配置管理类"""
    
    def __init__(self, config_path: str = "config.yaml"):
        self.config_path = config_path
        self.config = self._load_config()
        self._setup_logging()
    
    def _load_config(self) -> Dict:
        """加载配置文件"""
        try:
            with open(self.config_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        except FileNotFoundError:
            print(f"配置文件 {self.config_path} 未找到，使用默认配置")
            return self._get_default_config()
        except Exception as e:
            print(f"加载配置文件失败: {e}，使用默认配置")
            return self._get_default_config()
    
    def _get_default_config(self) -> Dict:
        """默认配置"""
        return {
            'llm': {
                'model': 'claude-3-5-sonnet-20241022',
                'max_tokens': 8192,
                'temperature': 0.1,
                'timeout': 300,
                'use_streaming': True,
                'stream_chunk_size': 2000
            },
            'tla_validator': {
                'tools_path': 'lib/tla2tools.jar',
                'timeout': 30
            },
            'generation': {
                'max_correction_attempts': 3
            },
            'paths': {
                'prompts_dir': 'src/prompts',
                'output_dir': 'output'
            },
            'logging': {
                'level': 'INFO',
                'format': '[%(levelname)s] %(message)s'
            }
        }
    
    def _setup_logging(self):
        """设置日志"""
        log_config = self.config.get('logging', {})
        level = getattr(logging, log_config.get('level', 'INFO'))
        format_str = log_config.get('format', '[%(levelname)s] %(message)s')
        
        logging.basicConfig(level=level, format=format_str, force=True)
    
    def get(self, key_path: str, default=None):
        """获取配置值，支持点分隔的路径，如 'llm.model'"""
        keys = key_path.split('.')
        value = self.config
        for key in keys:
            if isinstance(value, dict) and key in value:
                value = value[key]
            else:
                return default
        return value

# 全局配置实例
config = Config()
logger = logging.getLogger(__name__)

class LLMClient:
    """Simple LLM client supporting Claude models"""
    
    def __init__(self, api_key: Optional[str] = None):
        self.model = config.get('llm.model')
        self.max_tokens = config.get('llm.max_tokens')
        self.temperature = config.get('llm.temperature')
        self.timeout = config.get('llm.timeout')
        self.use_streaming = config.get('llm.use_streaming')
        self.stream_chunk_size = config.get('llm.stream_chunk_size')
        
        self.api_key = api_key or os.getenv("ANTHROPIC_API_KEY")
        if not self.api_key:
            raise ValueError("Claude API key not found. Set ANTHROPIC_API_KEY environment variable.")
    
        logger.info(f"初始化 LLM 客户端 - 模型: {self.model}, max_tokens: {self.max_tokens}, temperature: {self.temperature}")
    
    def generate(self, prompt: str, max_tokens: Optional[int] = None, temperature: Optional[float] = None) -> str:
        """Generate response using Claude API"""
        try:
            import anthropic
        except ImportError:
            raise ImportError("anthropic package not installed. Run: pip install anthropic")
        
        # 使用传入参数或配置文件中的默认值
        max_tokens = max_tokens or self.max_tokens
        temperature = temperature or self.temperature
        
        logger.info(f"开始生成 - 使用参数: max_tokens={max_tokens}, temperature={temperature}")
        
        client = anthropic.Anthropic(api_key=self.api_key)
        
        try:
            if self.use_streaming:
                return self._generate_streaming(client, prompt, max_tokens, temperature)
            else:
                return self._generate_standard(client, prompt, max_tokens, temperature)
                
        except Exception as e:
            logger.error(f"生成失败: {e}")
            # 如果流式处理失败，尝试标准处理
            if self.use_streaming:
                logger.info("流式处理失败，尝试标准处理...")
                return self._generate_standard(client, prompt, max_tokens, temperature)
            else:
                raise
    
    def _generate_streaming(self, client, prompt: str, max_tokens: int, temperature: float) -> str:
        """流式生成"""
        logger.info("开始流式生成...")
        response_text = ""
        
        with client.messages.stream(
            model=self.model,
            max_tokens=max_tokens,
            temperature=temperature,
            messages=[{"role": "user", "content": prompt}]
        ) as stream:
            for text in stream.text_stream:
                response_text += text
                # 显示进度
                if len(response_text) % self.stream_chunk_size == 0:
                    logger.debug(f"已生成 {len(response_text)} 个字符...")
        
        logger.info(f"流式生成完成，总长度: {len(response_text)} 个字符")
        return response_text
            
    def _generate_standard(self, client, prompt: str, max_tokens: int, temperature: float) -> str:
        """标准生成"""
        logger.info("开始标准生成...")
        
        response = client.messages.create(
            model=self.model,
            max_tokens=max_tokens,
            temperature=temperature,
            messages=[{"role": "user", "content": prompt}]
        )
        
        result = response.content[0].text
        logger.info(f"标准生成完成，长度: {len(result)} 个字符")
        return result

class TLAValidator:
    """TLA+ SANY validator"""
    
    def __init__(self):
        self.tla_tools_path = config.get('tla_validator.tools_path')
        self.timeout = config.get('tla_validator.timeout')
        
        if not os.path.exists(self.tla_tools_path):
            raise FileNotFoundError(f"TLA+ tools not found at {self.tla_tools_path}")
    
    def validate(self, tla_file: str) -> Tuple[bool, str]:
        """Validate TLA+ specification using SANY"""
        try:
            # Run SANY validation
            cmd = [
                "java", "-cp", self.tla_tools_path,
                "tla2sany.SANY", tla_file
            ]
            
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=self.timeout
            )
            
            success = result.returncode == 0
            output = result.stdout + result.stderr
            
            return success, output
            
        except subprocess.TimeoutExpired:
            return False, f"SANY validation timed out after {self.timeout} seconds"
        except Exception as e:
            return False, f"SANY validation failed: {e}"

class Phase1Generator:
    """Main Phase 1 generator class"""
    
    def __init__(self):
        self.llm = LLMClient()
        self.validator = TLAValidator()
        self.prompts_dir = Path(config.get('paths.prompts_dir'))
        self.max_correction_attempts = config.get('generation.max_correction_attempts')
        self.generation_mode = config.get('generation.mode', 'direct')
        
        # Load prompts based on generation mode
        if self.generation_mode == "draft-based":
            self.step0_prompt = self._load_prompt("step0_draft_generation.txt")
            self.step1_prompt = self._load_prompt("step1_code_translation_with_draft.txt")
        else:
            self.step1_prompt = self._load_prompt("step1_code_translation.txt")
        
        self.step2_prompt = self._load_prompt("step2_error_correction.txt")
    
    def _load_prompt(self, filename: str) -> str:
        """Load prompt template from file"""
        prompt_path = self.prompts_dir / filename
        if not prompt_path.exists():
            raise FileNotFoundError(f"Prompt file not found: {prompt_path}")
        
        with open(prompt_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def _read_source_code(self, input_path: str) -> str:
        """Read source code from file"""
        with open(input_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def _extract_tla_code(self, response: str) -> str:
        """Extract TLA+ code from LLM response"""
        # First, try to find code in markdown blocks
        lines = response.split('\n')
        in_code_block = False
        tla_lines = []
        
        for line in lines:
            if line.strip().startswith('```tla') or line.strip().startswith('```'):
                in_code_block = True
                continue
            elif line.strip() == '```' and in_code_block:
                in_code_block = False
                continue
            elif in_code_block:
                tla_lines.append(line)
            elif line.strip().startswith('----') and 'MODULE' in line:
                # Start of TLA+ module - collect everything until ====
                tla_lines = [line]
                for remaining_line in lines[lines.index(line)+1:]:
                    tla_lines.append(remaining_line)
                    if remaining_line.strip() == '====':
                        break
                break
        
        # If no code block found, try to extract the entire response as TLA+
        if not tla_lines:
            # Look for module start and end
            response_lines = response.split('\n')
            start_idx = -1
            end_idx = -1
            
            for i, line in enumerate(response_lines):
                if line.strip().startswith('----') and 'MODULE' in line:
                    start_idx = i
                elif line.strip() == '====' and start_idx != -1:
                    end_idx = i
                    break
            
            if start_idx != -1 and end_idx != -1:
                tla_lines = response_lines[start_idx:end_idx+1]
            else:
                # Last resort: assume the entire response is TLA+ code
                tla_lines = response_lines
        
        return '\n'.join(tla_lines)
    
    def _extract_module_name(self, tla_code: str) -> str:
        """Extract module name from TLA+ code"""
        lines = tla_code.split('\n')
        for line in lines:
            if line.strip().startswith('----') and 'MODULE' in line:
                # Extract module name from ---- MODULE ModuleName ----
                parts = line.strip().split()
                if len(parts) >= 3 and parts[1] == 'MODULE':
                    return parts[2]
        return "Generated"
    
    def step0_generate_draft(self, source_code: str) -> str:
        """Step 0: Generate natural language draft analysis"""
        logger.info("Step 0: 生成自然语言分析草稿...")
        
        prompt = self.step0_prompt.format(source_code=source_code)
        response = self.llm.generate(prompt)
        
        if not response.strip():
            raise ValueError("Failed to generate draft analysis from LLM response")
        
        return response
    
    def step1_translate_code(self, source_code: str, draft_analysis: str = "") -> str:
        """Step 1: Translate source code to TLA+ specification"""
        logger.info("Step 1: 将源代码翻译为 TLA+ 规范...")
        
        if self.generation_mode == "draft-based" and draft_analysis:
            prompt = self.step1_prompt.format(
                draft_analysis=draft_analysis,
                source_code=source_code
            )
        else:
            prompt = self.step1_prompt.format(source_code=source_code)
        
        response = self.llm.generate(prompt)
        
        tla_spec = self._extract_tla_code(response)
        if not tla_spec.strip():
            raise ValueError("Failed to extract TLA+ specification from LLM response")
        
        return tla_spec
    
    def step2_correct_errors(self, original_spec: str, error_messages: str, 
                           knowledge_context: str = "") -> str:
        """Step 2: Correct TLA+ specification errors"""
        logger.info("Step 2: 修正 TLA+ 规范错误...")
        
        prompt = self.step2_prompt.format(
            original_spec=original_spec,
            error_messages=error_messages,
            knowledge_context=knowledge_context
        )
        
        response = self.llm.generate(prompt)
        corrected_spec = self._extract_tla_code(response)
        
        if not corrected_spec.strip():
            raise ValueError("Failed to extract corrected TLA+ specification from LLM response")
        
        return corrected_spec
    
    def generate_specification(self, input_path: str, output_dir: str) -> Dict:
        """Generate TLA+ specification from source code"""
        logger.info(f"从 {input_path} 生成 TLA+ 规范")
        
        # Create output directory
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Read source code
        source_code = self._read_source_code(input_path)
        
        # Step 0: Generate draft analysis (if using draft-based mode)
        draft_analysis = ""
        if self.generation_mode == "draft-based":
            draft_analysis = self.step0_generate_draft(source_code)
            
            # Save draft analysis
            draft_file = output_path / "draft_analysis.txt"
            with open(draft_file, 'w', encoding='utf-8') as f:
                f.write(draft_analysis)
            logger.info(f"草稿分析保存到 {draft_file}")
        
        # Step 1: Translate code
        step1_spec = self.step1_translate_code(source_code, draft_analysis)
        
        # Extract module name and create appropriate filename
        module_name = self._extract_module_name(step1_spec)
        step1_file = output_path / f"{module_name}.tla"
        
        # Save Step 1 output
        with open(step1_file, 'w', encoding='utf-8') as f:
            f.write(step1_spec)
        
        logger.info(f"Step 1 输出保存到 {step1_file}")
        
        # Validate Step 1 output
        success, error_output = self.validator.validate(str(step1_file))
        
        if success:
            logger.info("Step 1 规范通过了 SANY 验证！")
            final_spec = step1_spec
            correction_attempts = 0
        else:
            logger.info("Step 1 规范有错误，进入 Step 2...")
            
            # Step 2: Correct errors
            current_spec = step1_spec
            correction_attempts = 0
            
            while correction_attempts < self.max_correction_attempts:
                correction_attempts += 1
                logger.info(f"修正尝试 {correction_attempts}/{self.max_correction_attempts}")
                
                # Load knowledge context (if available)
                knowledge_context = self._load_knowledge_context()
                
                # Correct errors
                corrected_spec = self.step2_correct_errors(
                    current_spec, error_output, knowledge_context
                )
                
                # Extract module name for corrected spec and save
                corrected_module_name = self._extract_module_name(corrected_spec)
                attempt_file = output_path / f"{corrected_module_name}_corrected.tla"
                with open(attempt_file, 'w', encoding='utf-8') as f:
                    f.write(corrected_spec)
                
                # Validate corrected specification
                success, error_output = self.validator.validate(str(attempt_file))
                
                if success:
                    logger.info(f"经过 {correction_attempts} 次尝试修正成功！")
                    final_spec = corrected_spec
                    break
                else:
                    logger.warning(f"修正尝试 {correction_attempts} 失败，重试...")
                    current_spec = corrected_spec
            
            if not success:
                logger.error(f"经过 {self.max_correction_attempts} 次尝试后仍未能修正规范")
                final_spec = current_spec
        
        # Save final specification
        final_module_name = self._extract_module_name(final_spec)
        final_file = output_path / f"{final_module_name}.tla"
        with open(final_file, 'w', encoding='utf-8') as f:
            f.write(final_spec)
        
        # Generate summary
        summary = {
            "input_file": input_path,
            "output_directory": str(output_path),
            "generation_mode": self.generation_mode,
            "step1_file": str(step1_file),
            "final_file": str(final_file),
            "validation_passed": success,
            "correction_attempts": correction_attempts,
            "final_errors": error_output if not success else None,
            "config_used": {
                "model": self.llm.model,
                "max_tokens": self.llm.max_tokens,
                "temperature": self.llm.temperature
            }
        }
        
        # Add draft file to summary if using draft-based mode
        if self.generation_mode == "draft-based":
            summary["draft_file"] = str(output_path / "draft_analysis.txt")
        
        # Save summary
        summary_file = output_path / "generation_summary.json"
        with open(summary_file, 'w', encoding='utf-8') as f:
            json.dump(summary, f, indent=2, ensure_ascii=False)
        
        logger.info(f"生成完成。最终规范: {final_file}")
        logger.info(f"摘要保存到: {summary_file}")
        
        return summary
    
    def _load_knowledge_context(self) -> str:
        """Load knowledge context for error correction"""
        # This could be enhanced to load from a knowledge base
        # For now, return basic TLA+ syntax reminders
        return """
Common TLA+ syntax patterns:
- Record access: record["field"] not record.field
- Sequence operations: Append(seq, elem), Head(seq), Tail(seq)
- Set operations: elem \\in set, set \\cup {elem}
- Variable updates: var' = new_value
- Unchanged variables: UNCHANGED <<var1, var2>>
- Quantifiers: \\E x \\in S : P(x), \\A x \\in S : P(x)
        """.strip()

def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(description="Phase 1: TLA+ Specification Generator")
    parser.add_argument("input", help="Input source code file")
    parser.add_argument("output", help="Output directory")
    parser.add_argument("--config", default="config.yaml", help="Configuration file path")
    parser.add_argument("--model", help="Override model from config")
    parser.add_argument("--max-tokens", type=int, help="Override max tokens from config")
    parser.add_argument("--temperature", type=float, help="Override temperature from config")
    parser.add_argument("--mode", choices=["direct", "draft-based"], 
                       help="Generation mode: 'direct' or 'draft-based'")
    parser.add_argument("--log-level", choices=["DEBUG", "INFO", "WARNING", "ERROR"], 
                       help="Override log level from config")
    
    args = parser.parse_args()
    
    try:
        # 重新加载配置（如果指定了不同的配置文件）
        if args.config != "config.yaml":
            global config
            config = Config(args.config)
        
        # 重新设置日志级别（如果指定了）
        if args.log_level:
            logging.getLogger().setLevel(getattr(logging, args.log_level))
    
        # Create generator
        generator = Phase1Generator()
        
        # 应用命令行参数覆盖
        if args.model:
            generator.llm.model = args.model
            logger.info(f"使用命令行指定的模型: {args.model}")
        
        if args.max_tokens:
            generator.llm.max_tokens = args.max_tokens
            logger.info(f"使用命令行指定的 max_tokens: {args.max_tokens}")
            
        if args.temperature:
            generator.llm.temperature = args.temperature
            logger.info(f"使用命令行指定的 temperature: {args.temperature}")
        
        if args.mode:
            generator.generation_mode = args.mode
            logger.info(f"使用命令行指定的生成模式: {args.mode}")
            
            # 重新加载对应的prompts
            if args.mode == "draft-based":
                generator.step0_prompt = generator._load_prompt("step0_draft_generation.txt")
                generator.step1_prompt = generator._load_prompt("step1_code_translation_with_draft.txt")
            else:
                generator.step1_prompt = generator._load_prompt("step1_code_translation.txt")
        
        # Generate specification
        summary = generator.generate_specification(args.input, args.output)
        
        # Print results
        print("\n" + "="*50)
        print("PHASE 1 GENERATION COMPLETE")
        print("="*50)
        print(f"Input: {summary['input_file']}")
        print(f"Output Directory: {summary['output_directory']}")
        print(f"Generation Mode: {summary['generation_mode']}")
        print(f"Final Specification: {summary['final_file']}")
        print(f"Validation Passed: {summary['validation_passed']}")
        print(f"Correction Attempts: {summary['correction_attempts']}")
        print(f"Model Used: {summary['config_used']['model']}")
        print(f"Max Tokens: {summary['config_used']['max_tokens']}")
        print(f"Temperature: {summary['config_used']['temperature']}")
        
        # 如果是草稿模式，显示草稿文件信息
        if summary.get('draft_file'):
            print(f"Draft Analysis: {summary['draft_file']}")
        
        if not summary['validation_passed']:
            print(f"Final Errors: {summary['final_errors']}")
            sys.exit(1)
        else:
            print("✅ Successfully generated valid TLA+ specification!")
            
    except Exception as e:
        logger.error(f"Generation failed: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main() 