import os
import yaml
import subprocess
import re

def tla_sany(file_path):
    # 运行tla_sany命令
    result = subprocess.run(['tla_sany', file_path], capture_output=True, text=True)
    output = result.stdout + result.stderr
    print(output)
    return output
    
def process_actions(yaml_file_path: str, output_dir: str):
    # 读取yaml文件
    with open(yaml_file_path, 'r') as f:
        yaml_data = yaml.safe_load(f)
    
    # 获取yaml文件名(不含扩展名)作为目录名
    base_name = os.path.splitext(os.path.basename(yaml_file_path))[0]
    # 创建动作目录
    action_dir = os.path.join(output_dir, f"{base_name}_actions")
    # 创建输出目录
    os.makedirs(action_dir, exist_ok=True)
    file_name = []
    # 处理每个动作
    for action in yaml_data.get('code', []):
        # 分割成行
        lines = action.strip().split('\n')                  
        
        # 安全过滤（列表推导式）
        lines = [line for line in lines 
                if line.strip() not in {'```tla+', '```tla', '```'}  # 删除代码块标记
                and not line.strip().startswith('\\*')]  # 删除转义注释
        
        if len(lines) == 0:
            continue
        # 获取动作名称(第一行中第一个==前的内容)
        action_name = lines[0].split('==')[0].strip()
        
        add_Module(action_name.split('(')[0], lines)

        # 写入文件
        action_file = os.path.join(action_dir, f"{action_name.split('(')[0]}.tla")
        with open(action_file, 'w') as f:
            f.write('\n'.join(lines))
        file_name.append(base_name + "_actions/" + action_name.split('(')[0] + ".tla")
    return file_name

def add_Module(module_name: str, lines: list):
    #插入前都要检查是否存在
    ext_flag = False
    module_flag = False
    end_flag = False
    for line in lines:
        if line.startswith("EXTENDS"):
            ext_flag = True
        elif line.startswith("----MODULE"):
            module_flag = True
        elif line.startswith("====\n"):
            end_flag = True
    if not ext_flag:
        lines.insert(0, "EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals")
    if not module_flag:
        lines.insert(0, f"----MODULE {module_name} ----")
    if not end_flag:
        lines.append("====\n")

def add_var_func(file_path: str):
    add_var(file_path)
    add_func(file_path)

def add_var(file_path: str):
    # 使用正则表达式提取Unknown operator后的变量名
    output = tla_sany(file_path)
    pattern = r"Unknown operator: `([^']*)'."
    matches = re.findall(pattern, output)
    
    # 转换为集合去重
    var_set = set(matches)
    
    if var_set:
        # 读取原文件内容
        with open(file_path, 'r') as f:
            lines = f.readlines()
        
        # 检查是否已存在VARIABLES声明
        var_line_idx = -1
        for i, line in enumerate(lines):
            if line.startswith("VARIABLES"):
                var_line_idx = i
                break
                
        # 构造新的VARIABLES声明
        var_str = "VARIABLES " + ", ".join(var_set) + "\n"
        
        # 如果存在则替换,否则插入到第2行
        if var_line_idx >= 0:
            lines[var_line_idx] = var_str
        else:
            lines.insert(2, var_str)
        
        # 写回文件
        with open(file_path, 'w') as f:
            f.writelines(lines)
    else :
        #第三行写入空行
        with open(file_path, 'r') as f:
            lines = f.readlines()
            lines.insert(2, "\n")
        # 写回文件
        with open(file_path, 'w') as f:
            f.writelines(lines)

def add_func(file_path: str):
    # 使用正则表达式提取需要0参数的函数名
    output = tla_sany(file_path)
    pattern = r"The operator ([^\s]*) requires 0 arguments"
    matches = re.findall(pattern, output)
    # matches 去重
    matches = list(set(matches))
    if matches:
        # 读取原文件内容
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        # 找到VARIABLES行
        for i, line in enumerate(lines):
            if line.startswith("VARIABLES"):
                # 获取所有变量
                vars = [v.strip() for v in line[9:].strip().split(",")]
                # 移除匹配到的函数名
                vars = [v for v in vars if v not in matches]
                # 重写VARIABLES行
                if vars:
                    lines[i] = "VARIABLES " + ", ".join(vars) + "\n"
                else:
                    lines.pop(i)
                break
                
        # 在第3行插入函数定义
        # 检查是否已存在相同的函数定义
        existing_funcs = []
        for line in lines:
            if "==" in line:
                func_name = line.split("==")[0].strip()
                if "(" in func_name:
                    existing_funcs.append(func_name.split("(")[0].strip())
        func_defs = []
        for func in matches:
            # 检查函数调用时的参数个数
            param_pattern = rf"{func}\((.*?)\)"
            param_matches = re.findall(param_pattern, "".join(lines))
            if param_matches:
                # 获取第一次调用时的参数个数
                params = [p.strip() for p in param_matches[0].split(",") if p.strip()]
                param_count = len(params)
                # 根据参数个数生成参数列表
                param_list = ", ".join([f"x{i+1}" for i in range(param_count)])
                func_defs.append(f"{func}({param_list}) == UNCHANGED <<{param_list}>>\n")
            else:
                #error
                print(f"Error: {func} has no parameters")
        
        if func_defs and func_defs not in existing_funcs:
            lines[3:3] = func_defs
            
        # 写回文件
        with open(file_path, 'w') as f:
            f.writelines(lines)

def complete_actions(input_dir: str, output_dir: str):
    file_name = process_actions(input_dir, output_dir)
    for name in file_name:
        add_var_func(os.path.join(output_dir, name))
    
