import os
import subprocess

def tla_sany(file_path):
    # 运行tla_sany命令
    result = subprocess.run(['tla_sany', file_path], capture_output=True, text=True)
    output = result.stdout + result.stderr
    print(output)
    
    # 创建日志文件路径
    log_file = '/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/sany_error.log'
    
    # 将输出写入日志文件
    with open(log_file, 'a') as f:
        f.write(f"\n=== TLA+ SANY 检查文件: {file_path} ===\n")
        f.write(output)
        f.write("\n")
        
    return output

if __name__ == "__main__":
    file_path = '/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/test_actions/'
    for file in os.listdir(file_path):
        if file.endswith('.tla'):
            tla_sany(file_path + file)