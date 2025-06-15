import os
import sys
from openai import OpenAI
import time
import json
from concurrent.futures import ThreadPoolExecutor  # 新增这行
from get_errors import complete_actions, tla_sany, add_var_func
import concurrent.futures
import threading
import argparse
import re
from pathlib import Path

UPDATE_ERROR = True

# 获取当前文件绝对路径
current_file = os.path.abspath(__file__)
# 计算项目根目录路径（LLM_gen/spec_rag_system）
project_root = os.path.dirname(os.path.dirname(os.path.dirname(current_file)))

# 添加项目根目录到Python路径
if project_root not in sys.path:
    sys.path.insert(0, project_root)
    
# 现在可以正确导入
from spec_rag_system.retrieval_system.retrievers.basic_retriever import ErrorRetriever

LOOPTIMES = 5

def parse_args():
    """解析命令行参数"""
    parser = argparse.ArgumentParser(description='批量处理配置')
    
    parser.add_argument('--error_data', type=str, 
                        default="/home/ubuntu/LLM_gen/spec_rag_system/knowledge_base/raw_errors/sany_errors/initial_errors.json",
                        help='错误数据文件路径')
    
    parser.add_argument('--code_folder', type=str,
                        default="/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/test_actions",
                        help='代码输入目录路径')
    
    parser.add_argument('--output_folder', type=str,
                        default="/home/ubuntu/LLM_gen/spec_rag_system/batch_processing",
                        help='输出目录路径')
    
    parser.add_argument('--exp2_prompt', type=str,
                        default="/home/ubuntu/LLM_gen/spec_rag_system/batch_processing/prompt/experiment2",
                        help='实验2提示词目录')
    
    parser.add_argument('--exp3_prompt', type=str,
                        default="/home/ubuntu/LLM_gen/spec_rag_system/batch_processing/prompt/experiment3",
                        help='实验3提示词目录')
    
    return parser.parse_args()

error_data_file_path = ""
code_folder_path = ""
output_folder_path = ""
exp2_prompt_folder_path = ""
exp3_prompt_folder_path = ""

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


# 创建输出目录结构
def create_output_dirs(output_folder_path):
    os.makedirs(output_folder_path, exist_ok=True)
    exp1_dir = os.path.join(output_folder_path, "experiment1/" + time.strftime("%Y%m%d_%H%M%S", time.localtime())) 
    exp2_dir = os.path.join(output_folder_path, "experiment2/" + time.strftime("%Y%m%d_%H%M%S", time.localtime()))
    exp3_dir = os.path.join(output_folder_path, "experiment3/" + time.strftime("%Y%m%d_%H%M%S", time.localtime()))
    
    for dir in [exp1_dir, exp2_dir, exp3_dir]:
        os.makedirs(dir, exist_ok=True)
        
    return exp1_dir, exp2_dir, exp3_dir

def run_experiment1(code_folder_path, output_dir):
    # 记录实验结果的文件
    results_file = os.path.join(output_dir, "compilation_results.txt")
    log_file = os.path.join(output_dir, "experiment1.log")
    
    passed_files = []
    failed_files = []
    
    # 遍历所有tla文件
    for file in os.listdir(code_folder_path):
        if file.endswith('.tla'):
            file_path = os.path.join(code_folder_path, file)
            
            # 调用complete_actions处理文件
            try:
                #complete_actions(file_path, output_dir)
                
                # 调用tla_sany进行编译
                output = tla_sany(file_path)
                
                # 检查是否有编译错误
                if "Error" not in output and "error" not in output:
                    passed_files.append(file)
                else:
                    failed_files.append((code_folder_path + "/" + file, output))
                    
            except Exception as e:
                # 记录错误日志
                with open(log_file, 'a') as f:
                    f.write(f"处理文件 {file} 时发生错误: {str(e)}\n")
    
    # 写入实验结果
    with open(results_file, 'a') as f:
        f.write(f"编译通过的文件数: {len(passed_files)}\n")
        f.write(f"编译失败的文件数: {len(failed_files)}\n\n")
        
        f.write("通过编译的文件:\n")
        for file in passed_files:
            f.write(f"- {file}\n")
            
        f.write("\n失败的文件及错误信息:\n")
        for file, error in failed_files:
            f.write(f"=== {file} ===\n{error}\n\n")
            
    return failed_files

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
        response_json = json.loads(response)
        spec = response_json.get("spec")
        if not spec:
            return None
            
        output_file = os.path.join(output_dir, os.path.basename(file))
        errors = response_json.get("errors", [])
        
        # 使用锁保证写入安全
        with write_lock:
            with open(output_file, 'w') as f:
                f.write(spec)
            with open(log_file, 'a') as f:
                f.write(f"已处理文件 {file} 并保存到 {output_file}\n")
                
        return output_file, errors
    except json.JSONDecodeError as e:
        with write_lock:
            with open(log_file, 'a') as f:
                f.write(f"解析文件 {file} 的响应时发生错误: {str(e)}\n")
                
        return None
    except Exception as e:
        with write_lock:
            with open(log_file, 'a') as f:
                f.write(f"处理文件 {file} 时发生未预期错误: {str(e)}\n")
        return None

def run_experiment2(failed_files, output_dir):
    # 读取prompt文件
    prompt_file = os.path.join(exp2_prompt_folder_path, "prompt.txt")
    
    results_file = os.path.join(output_dir, "compilation_results.txt")
    log_file = os.path.join(output_dir, "experiment2.log")
    
    # 检查prompt文件是否存在
    if not os.path.exists(prompt_file):
        raise FileNotFoundError("未找到所需的prompt文件")
        
    # 读取prompt文件内容
    with open(prompt_file, 'r') as f:
        prompt = f.read()


    # # 修改后的主处理逻辑
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
        futures = []
        for file, error in failed_files:
            future = executor.submit(
                process_single_file,
                file, error, output_dir, log_file, prompt
            )
            futures.append(future)
        
        # 等待所有任务完成
        for future in concurrent.futures.as_completed(futures):
            result, errors= future.result()
            if result:
                print(f"成功处理: {result}")

    # 运行tla_sany检查修正后的文件
    fixed_files = [f for f in os.listdir(output_dir) if f.endswith('.tla')]
    still_failed = []
    failed_files = []
    for file in fixed_files:
        file_path = os.path.join(output_dir, file)

        add_var_func(file_path)
        # 运行tla_sany
        result = tla_sany(file_path)
        # 检查是否有编译错误
        if "Error" not in result and "error" not in result:
            print(f"文件 {file} 编译通过")
        else:
            still_failed.append((file_path, result))
            failed_files.append((output_dir + "/" + file, result))
            with open(log_file, 'a') as f:
                f.write(f"文件 {file} 仍有编译错误:\n{result}\n")
                
    # 记录编译结果统计
    with open(results_file, 'a') as f:
        f.write(f"编译通过的文件数: {len(fixed_files) - len(still_failed)}\n")
        f.write(f"编译失败的文件数: {len(still_failed)}\n\n")
        
        # 记录通过编译的文件
        f.write("通过编译的文件:\n")
        for file in fixed_files:
            if not any(file in failed[0] for failed in still_failed):
                f.write(f"- {file}\n")
        f.write("\n")
        
        # 记录失败的文件及错误信息
        if still_failed:
            f.write("失败的文件及错误信息:\n")
            for file, error in still_failed:
                f.write(f"=== {file} ===\n{error}\n\n")
    return failed_files

def get_error_info(error):
    # 判断错误类型并提取相关信息
    error_info = ""
    
    if "***Parse Error***" in error:
        # 解析错误
        lines = error.split('\n')
        start_idx = -1
        end_idx = -1
        
        for i, line in enumerate(lines):
            if "***Parse Error***" in line:
                start_idx = i + 1
            if "Residual stack trace follows:" in line:
                end_idx = i
                break
                
        if start_idx != -1 and end_idx != -1:
            error_info = "\n".join(lines[start_idx:end_idx])
        else:
            error_info = error
            print(f"找不到错误信息")

    elif "*** Errors:" in error:
        # 语义错误
        lines = error.split('\n')
        start_idx = -1
        
        for i, line in enumerate(lines):
            if "*** Errors:" in line:
                start_idx = i + 1
                break
                
        if start_idx != -1:
            error_info = "\n".join(lines[start_idx:])
        else:
            error_info = error
            print(f"找不到错误信息")
            
    return error_info.strip()

def get_exp_prompt(results):
    prompt = ""
    for i, result in enumerate(results, 1):
        prompt += f"Solution {i}:\n"
        prompt += f"Error message: {result['error_message']}\n"
        prompt += f"Solution: {result['solution']}\n"
        prompt += f"Context: {result['context']}\n\n"
    return prompt

def update_errors_database(new_errors, error_data_file_path):
    # 确保文件存在
    Path(error_data_file_path).touch(exist_ok=True)
    
    # 读取现有数据
    try:
        with open(error_data_file_path, 'r') as f:
            existing_errors = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        existing_errors = []

    # 步骤1：获取当前最大错误序号
    max_id = 0
    id_pattern = re.compile(r'^E(\d+)$', re.IGNORECASE)  # 兼容大小写
    for err in existing_errors:
        if match := id_pattern.match(err.get("error_id", "")):
            current_num = int(match.group(1))
            max_id = max(max_id, current_num)

    # 步骤2：分配新序号
    for new_err in new_errors:
        # 检查是否已有合法ID
        if "error_id" in new_err:
            if id_pattern.match(new_err["error_id"]):
                # 检查ID是否已存在
                existing_ids = {e["error_id"].upper() for e in existing_errors}
                if new_err["error_id"].upper() in existing_ids:
                    # ID冲突时自动分配新号
                    max_id += 1
                    new_err["error_id"] = f"E{max_id:03d}"
                else:
                    # 更新最大ID（处理不连续情况）
                    if match := id_pattern.match(new_err["error_id"]):
                        current_num = int(match.group(1))
                        max_id = max(max_id, current_num)
            else:
                # 非法格式时自动分配
                max_id += 1
                new_err["error_id"] = f"E{max_id:03d}"
        else:
            # 自动分配新ID
            max_id += 1
            new_err["error_id"] = f"E{max_id:03d}"

    # 步骤3：追加新数据
    updated_errors = existing_errors + new_errors

    # 写回文件
    with open(error_data_file_path, 'w') as f:
        json.dump(updated_errors, f, indent=2, ensure_ascii=False)

def run_experiment3(failed_files, error_data_file_path, output_dir):
    prompt_file = os.path.join(exp3_prompt_folder_path, "prompt.txt")
    
    results_file = os.path.join(output_dir, "compilation_results.txt")
    log_file = os.path.join(output_dir, "experiment3.log")

    # 检查prompt文件是否存在
    if not os.path.exists(prompt_file):
        raise FileNotFoundError("未找到所需的prompt文件")
        
    # 读取prompt文件内容
    with open(prompt_file, 'r') as f:
        prompt = f.read()

    # 初始化检索器
    retriever = ErrorRetriever(error_data_file_path)
    
    errors_map = {}

    # # 修改后的主处理逻辑
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
        futures = []
        for file, error in failed_files:
            query = get_error_info(error)
            results = retriever.search(query, top_k=3)
            # 将结果写入日志
            log_file = os.path.join(output_dir, "experiment3.log")
            with open(log_file, 'a') as f:
                f.write(f"检索结果示例:\n{json.dumps(results, indent=2)}")

            # 获取检索结果中的错误信息
            example_info = get_exp_prompt(results)

            future = executor.submit(
                process_single_file,
                file, error, output_dir, log_file, prompt, example_info
            )
            futures.append(future)
        
        # 等待所有任务完成
        for future in concurrent.futures.as_completed(futures):
            result, errors = future.result()
            if result:
                print(f"成功处理: {result}")
                errors_map[result] = errors


    fixed_files = [f for f in os.listdir(output_dir) if f.endswith('.tla')]
    still_failed = []
    failed_files = []

    for file in fixed_files:
        file_path = os.path.join(output_dir, file)

        add_var_func(file_path)
        # 运行tla_sany
        result = tla_sany(file_path)
        # 检查是否有编译错误
        if "Error" not in result and "error" not in result:
            if UPDATE_ERROR:
                if file_path in errors_map:
                    update_errors_database(errors_map[file_path], error_data_file_path)
                else:
                    print(f"在此之前已经处理过文件 {file_path}")
            print(f"文件 {file} 编译通过")
        else:
            still_failed.append((file_path, result))
            failed_files.append((output_dir + "/" + file, result))
            with open(log_file, 'a') as f:
                f.write(f"文件 {file} 仍有编译错误:\n{result}\n")
                
    # 记录编译结果统计
    with open(results_file, 'a') as f:
        f.write(f"编译通过的文件数: {len(fixed_files) - len(still_failed)}\n")
        f.write(f"编译失败的文件数: {len(still_failed)}\n\n")
        
        # 记录通过编译的文件
        f.write("通过编译的文件:\n")
        for file in fixed_files:
            if not any(file in failed[0] for failed in still_failed):
                f.write(f"- {file}\n")
        f.write("\n")
        
        # 记录失败的文件及错误信息
        if still_failed:
            f.write("失败的文件及错误信息:\n")
            for file, error in still_failed:
                f.write(f"=== {file} ===\n{error}\n\n")

    return failed_files

def run_all_experiments(code_folder_path, output_folder_path, error_data_file_path):
    # 创建输出目录
    exp1_dir, exp2_dir, exp3_dir = create_output_dirs(output_folder_path)
    # 清空日志文件
    with open(os.path.join(exp1_dir, "experiment1.log"), 'w') as f:
        f.write("")
    with open(os.path.join(exp2_dir, "experiment2.log"), 'w') as f:
        f.write("")
    with open(os.path.join(exp3_dir, "experiment3.log"), 'w') as f:
        f.write("")
    # 运行实验1
    print("开始运行实验1...")
    failed_files_2 = run_experiment1(code_folder_path, exp1_dir)
    failed_files_3 = failed_files_2
    # 运行实验2
    # print("开始运行实验2...")
    # for i in range(LOOPTIMES):
    #     failed_files_2 = run_experiment2(failed_files_2, exp2_dir)
    
    # 运行实验3
    print("开始运行实验3...")
    for i in range(LOOPTIMES):
        failed_files_3 = run_experiment3(failed_files_3, error_data_file_path, exp3_dir)

if __name__ == "__main__":
    args = parse_args()
    
    # 使用参数或默认值
    error_data_file_path = args.error_data
    code_folder_path = args.code_folder
    output_folder_path = args.output_folder
    exp2_prompt_folder_path = args.exp2_prompt
    exp3_prompt_folder_path = args.exp3_prompt
    run_all_experiments(args.code_folder, args.output_folder, args.error_data)
