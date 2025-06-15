import os
import re
asterinas_mutex_path = "/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/asterinas/mutex"
asterinas_spinLock_path = "/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/asterinas/spinLock"
asterinas_rwmutex_path = "/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/asterinas/rwmutex"
etcd_path = "/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/etcd"
pySyncObj_path = "/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/pySyncObj"
raft_java_path = "/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/raft-java"

output_dir_path = "/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/spec"

def extract_tla_functions(input_dir, output_file):
    """
    提取所有TLA文件中的同名函数到统一文件
    :param input_dir: 包含.tla文件的目录
    :param output_file: 合并后的输出文件路径
    """
    function_store = {}
    
    # 遍历目录处理文件
    for filename in os.listdir(input_dir):
        if not filename.endswith(".tla"):
            continue
        
        # 从文件名提取函数名
        func_name = os.path.splitext(filename)[0]
        filepath = os.path.join(input_dir, filename)
        
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
            # 使用正则表达式提取目标函数
            pattern = re.compile(
                r'^{}\([^)]*\)\s*==\n((?:^[ \t]+.*\n?)*)'.format(re.escape(func_name)),
                re.MULTILINE
            )
            match = pattern.search(content)
            
            if match:
                # 清理首尾空行并保留缩进
                func_body = '\n'.join([line.rstrip() for line in match.group(0).split('\n')])
                function_store[func_name] = func_body 
    
    # 生成合并文件
    with open(output_file, 'w', encoding='utf-8') as f:
        
        # 写入所有函数
        for func in function_store:
            f.write(function_store[func] + '\n\n')



if __name__ == "__main__":
    extract_tla_functions(asterinas_spinLock_path, os.path.join(output_dir_path, "spinLock=.tla"))
