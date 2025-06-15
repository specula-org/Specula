import time
import threading
from openai import OpenAI
import concurrent.futures
import sys
import os
import yaml

prompt_PATH="/home/ubuntu/LLM_gen/spec_rag_system/baseline/prompt.txt"
client = OpenAI(
    base_url = "https://api.deepseek.com",
    api_key = "sk-2dc693d4f70c429ca14e9eb3e23c6124"
)

# 创建线程安全的锁
write_lock = threading.Lock()

def get_completion(prompt, content):
    while True:
        try:
            # 添加请求开始日志
            print(f"\n[DEBUG] 开始API请求，代码块长度: {len(content)} 字符")
            print(f"[DEBUG] 使用的Prompt前缀: {prompt[:50]}...")  # 显示前50字符
            
            completion = client.chat.completions.create(
                model="deepseek-reasoner",
                messages=[
                    {"role": "system", "content": prompt},
                    {"role": "user", "content": content}
                ],
                temperature=0.1,
                #top_p=0.1,
                #frequency_penalty=1,
                #presence_penalty=1,
                max_tokens=8192,
                stream=True  # 启用流式输出
            )
            try:
                full_response = ""
                chunk_count = 0
                start_time = time.time()
                
                for chunk in completion:
                    chunk_count += 1
                    # 打印流式接收状态
                    if chunk_count % 1000 == 0:
                        print(f"[DEBUG] 已接收 {chunk_count} 个数据块，耗时 {time.time()-start_time:.2f}s")
                        
                    if chunk.choices[0].delta.content is not None:
                        full_response += chunk.choices[0].delta.content
                
                # 添加响应统计日志    
                print(f"[SUCCESS] 请求完成，共接收 {chunk_count} 个数据块")
                print(f"[RESPONSE] 响应首行: {full_response.splitlines()[0][:50]}...")
                return full_response
                
            except Exception as e:
                print(f"[ERROR] 流式处理异常: {str(e)}")
                print(f"[DUMP] 最后收到的数据块: {chunk}")  # 打印异常时的chunk
                time.sleep(5)
                
        except Exception as e:
            print(f"[FATAL] API请求失败: {e}")
            print(f"[DUMP] 当前内容: {content[:100]}...")  # 截断前100字符
            time.sleep(60)

def process_single_file(file, error, output_dir, log_file, prompt, example_info=None):
    """处理单个文件的线程任务"""
    try:
        with open(file, 'r') as f:
            code = f.read()
        if example_info:
            response = get_completion(prompt, "error: \n" + error + "\n" + "code: \n" + code + "\n" + "example_info: \n" + example_info)
        else:
            response = get_completion(prompt, "error: \n" + error + "\n" + "code: \n" + code)
        with open(log_file, 'a') as f:
            f.write(f"文件 {file} 的完整响应:\n{response}\n\n")
            
        output_file = output_PATH
        
        # 使用锁保证写入安全
        with write_lock:
            with open(output_file, 'w') as f:
                f.write(response)
            with open(log_file, 'a') as f:
                f.write(f"已处理文件 {file} 并保存到 {output_file}\n")
                
        return output_file
    except Exception as e:
        with write_lock:
            with open(log_file, 'a') as f:
                f.write(f"处理文件 {file} 时发生未预期错误: {str(e)}\n")
        return None

def split_code_gen_spec(prompt, code_list):
    result = ""
    for i in range(len(code_list)):
        p = "Because of the token limit, I converted this function into a TLA+ specification task divided into multiple parts, and what you need to complete now is the %d-th task, the previously generated content is as follows:" % (i+1)
        result += get_completion(prompt, p + result + "code:\n" + code_list[i])
    return result

def load_yaml(file_path):
    """加载YAML文件并返回其内容"""
    with open(file_path, 'r') as f:
        return yaml.safe_load(f)

if __name__ == "__main__":
    with open(prompt_PATH, "r") as f:
        prompt = f.read()
    # 获取命令行参数
    if len(sys.argv) < 3:
        print("请提供代码路径和输出路径作为参数")
        sys.exit(1)
        
    code_PATH = sys.argv[1]
    output_PATH = sys.argv[2]
    
    # 确保输出目录存在
    os.makedirs(os.path.dirname(output_PATH), exist_ok=True)
    code = load_yaml(code_PATH) 
    
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
        # 创建任务列表
        futures = []
        for i in range(len(code)):
            # 提交任务到线程池
            if type(code[i]['code']) != list:
                future = executor.submit(get_completion, prompt, code[i]['code'])
                futures.append(future)
            else:
                future = executor.submit(split_code_gen_spec, prompt, code[i]['code'])
                futures.append(future)
        
        # 等待所有任务完成并按顺序收集结果
        results = []
        for future in futures:
            try:
                result = future.result()
                results.append(result)
            except Exception as e:
                print(f"[ERROR] 任务执行失败: {e}")
                results.append("")  # 失败时添加空字符串保持顺序

        # 按顺序写入结果
        with open(output_PATH, 'w') as f:
            for result in results:
                f.write(result + '\n')
