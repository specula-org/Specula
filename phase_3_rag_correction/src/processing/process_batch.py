import os
import sys
from openai import OpenAI
import time
import json
from concurrent.futures import ThreadPoolExecutor
from get_errors import complete_actions, tla_sany, add_var_func
import concurrent.futures
import threading
import argparse
import re
from pathlib import Path

UPDATE_ERROR = True

# Get current file absolute path
current_file = os.path.abspath(__file__)
# Calculate project root directory path (LLM_gen/spec_rag_system)
project_root = os.path.dirname(os.path.dirname(os.path.dirname(current_file)))

# Add project root directory to Python path
if project_root not in sys.path:
    sys.path.insert(0, project_root)
    
# Now can import correctly
from spec_rag_system.retrieval_system.retrievers.basic_retriever import ErrorRetriever

LOOPTIMES = 5

def parse_args():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(description='Batch processing configuration')
    
    parser.add_argument('--error_data', type=str, 
                        default="/home/ubuntu/LLM_gen/spec_rag_system/knowledge_base/raw_errors/sany_errors/initial_errors.json",
                        help='Error data file path')
    
    parser.add_argument('--code_folder', type=str,
                        default="/home/ubuntu/LLM_gen/spec_rag_system/data_gen/output/test_actions",
                        help='Code input directory path')
    
    parser.add_argument('--output_folder', type=str,
                        default="/home/ubuntu/LLM_gen/spec_rag_system/batch_processing",
                        help='Output directory path')
    
    parser.add_argument('--exp2_prompt', type=str,
                        default="/home/ubuntu/LLM_gen/spec_rag_system/batch_processing/prompt/experiment2",
                        help='Experiment 2 prompt directory')
    
    parser.add_argument('--exp3_prompt', type=str,
                        default="/home/ubuntu/LLM_gen/spec_rag_system/batch_processing/prompt/experiment3",
                        help='Experiment 3 prompt directory')
    
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

# Create thread-safe lock
write_lock = threading.Lock()

def get_completion(prompt, content):
    while True:
        try:
            # Add request start log
            print(f"\n[DEBUG] Starting API request, code block length: {len(content)} characters")
            print(f"[DEBUG] Using prompt prefix: {prompt[:50]}...")  # Show first 50 characters
            
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
                stream=True  # Enable streaming output
            )
            try:
                full_response = ""
                chunk_count = 0
                start_time = time.time()
                
                for chunk in completion:
                    chunk_count += 1
                    # Print streaming reception status
                    if chunk_count % 1000 == 0:
                        print(f"[DEBUG] Received {chunk_count} chunks, elapsed time: {time.time()-start_time:.2f}s")
                        
                    if chunk.choices[0].delta.content is not None:
                        full_response += chunk.choices[0].delta.content
                
                # Add response statistics log    
                print(f"[SUCCESS] Request completed, received {chunk_count} chunks total")
                print(f"[RESPONSE] First line of response: {full_response.splitlines()[0][:50]}...")
                return full_response
                
            except Exception as e:
                print(f"[ERROR] Streaming processing exception: {str(e)}")
                print(f"[DUMP] Last received chunk: {chunk}")  # Print chunk when exception occurs
                time.sleep(5)
                
        except Exception as e:
            print(f"[FATAL] API request failed: {e}")
            print(f"[DUMP] Current content: {content[:100]}...")  # Truncate to first 100 characters
            time.sleep(60)


# Create output directory structure
def create_output_dirs(output_folder_path):
    os.makedirs(output_folder_path, exist_ok=True)
    exp1_dir = os.path.join(output_folder_path, "experiment1/" + time.strftime("%Y%m%d_%H%M%S", time.localtime())) 
    exp2_dir = os.path.join(output_folder_path, "experiment2/" + time.strftime("%Y%m%d_%H%M%S", time.localtime()))
    exp3_dir = os.path.join(output_folder_path, "experiment3/" + time.strftime("%Y%m%d_%H%M%S", time.localtime()))
    
    for dir in [exp1_dir, exp2_dir, exp3_dir]:
        os.makedirs(dir, exist_ok=True)
        
    return exp1_dir, exp2_dir, exp3_dir

def run_experiment1(code_folder_path, output_dir):
    # Record experiment results file
    results_file = os.path.join(output_dir, "compilation_results.txt")
    log_file = os.path.join(output_dir, "experiment1.log")
    
    passed_files = []
    failed_files = []
    
    # Iterate through all tla files
    for file in os.listdir(code_folder_path):
        if file.endswith('.tla'):
            file_path = os.path.join(code_folder_path, file)
            
            # Call complete_actions to process file
            try:
                #complete_actions(file_path, output_dir)
                
                # Call tla_sany to compile
                output = tla_sany(file_path)
                
                # Check if there are compilation errors
                if "Error" not in output and "error" not in output:
                    passed_files.append(file)
                else:
                    failed_files.append((code_folder_path + "/" + file, output))
                    
            except Exception as e:
                # Record error log
                with open(log_file, 'a') as f:
                    f.write(f"Error processing file {file}: {str(e)}\n")
    
    # Write experiment results
    with open(results_file, 'a') as f:
        f.write(f"Files passed compilation: {len(passed_files)}\n")
        f.write(f"Files failed compilation: {len(failed_files)}\n\n")
        
        f.write("Files that passed compilation:\n")
        for file in passed_files:
            f.write(f"- {file}\n")
            
        f.write("\nFailed files and error information:\n")
        for file, error in failed_files:
            f.write(f"=== {file} ===\n{error}\n\n")
            
    return failed_files

def process_single_file(file, error, output_dir, log_file, prompt, example_info=None):
    """Thread task for processing a single file"""
    try:
        with open(file, 'r') as f:
            code = f.read()
        if example_info:
            response = get_completion(prompt, "error: \n" + error + "\n" + "code: \n" + code + "\n" + "example_info: \n" + example_info)
        else:
            response = get_completion(prompt, "error: \n" + error + "\n" + "code: \n" + code)
        with open(log_file, 'a') as f:
            f.write(f"Complete response for file {file}:\n{response}\n\n")
        response_json = json.loads(response)
        spec = response_json.get("spec")
        if not spec:
            return None
            
        output_file = os.path.join(output_dir, os.path.basename(file))
        errors = response_json.get("errors", [])
        
        # Use lock to ensure write safety
        with write_lock:
            with open(output_file, 'w') as f:
                f.write(spec)
            with open(log_file, 'a') as f:
                f.write(f"Processed file {file} and saved to {output_file}\n")
                
        return output_file, errors
    except json.JSONDecodeError as e:
        with write_lock:
            with open(log_file, 'a') as f:
                f.write(f"Error parsing response for file {file}: {str(e)}\n")
                
        return None
    except Exception as e:
        with write_lock:
            with open(log_file, 'a') as f:
                f.write(f"Unexpected error processing file {file}: {str(e)}\n")
        return None

def run_experiment2(failed_files, output_dir):
    # Read prompt file
    prompt_file = os.path.join(exp2_prompt_folder_path, "prompt.txt")
    
    results_file = os.path.join(output_dir, "compilation_results.txt")
    log_file = os.path.join(output_dir, "experiment2.log")
    
    # Check if prompt file exists
    if not os.path.exists(prompt_file):
        raise FileNotFoundError("Required prompt file not found")
        
    # Read prompt file content
    with open(prompt_file, 'r') as f:
        prompt = f.read()


    # Modified main processing logic
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
        futures = []
        for file, error in failed_files:
            future = executor.submit(
                process_single_file,
                file, error, output_dir, log_file, prompt
            )
            futures.append(future)
        
        # Wait for all tasks to complete
        for future in concurrent.futures.as_completed(futures):
            result, errors= future.result()
            if result:
                print(f"Successfully processed: {result}")

    # Run tla_sany to check corrected files
    fixed_files = [f for f in os.listdir(output_dir) if f.endswith('.tla')]
    still_failed = []
    failed_files = []
    for file in fixed_files:
        file_path = os.path.join(output_dir, file)

        add_var_func(file_path)
        # Run tla_sany
        result = tla_sany(file_path)
        # Check if there are compilation errors
        if "Error" not in result and "error" not in result:
            print(f"File {file} passed compilation")
        else:
            still_failed.append((file_path, result))
            failed_files.append((output_dir + "/" + file, result))
            with open(log_file, 'a') as f:
                f.write(f"File {file} still has compilation errors:\n{result}\n")
                
    # Record compilation result statistics
    with open(results_file, 'a') as f:
        f.write(f"Files passed compilation: {len(fixed_files) - len(still_failed)}\n")
        f.write(f"Files failed compilation: {len(still_failed)}\n\n")
        
        # Record files that passed compilation
        f.write("Files that passed compilation:\n")
        for file in fixed_files:
            if not any(file in failed[0] for failed in still_failed):
                f.write(f"- {file}\n")
        f.write("\n")
        
        # Record failed files and error information
        if still_failed:
            f.write("Failed files and error information:\n")
            for file, error in still_failed:
                f.write(f"=== {file} ===\n{error}\n\n")
    return failed_files

def get_error_info(error):
    # Determine error type and extract relevant information
    error_info = ""
    
    if "***Parse Error***" in error:
        # Parse error
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
            print(f"Cannot find error information")

    elif "*** Errors:" in error:
        # Semantic error
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
            print(f"Cannot find error information")
            
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
    # Ensure file exists
    Path(error_data_file_path).touch(exist_ok=True)
    
    # Read existing data
    try:
        with open(error_data_file_path, 'r') as f:
            existing_errors = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        existing_errors = []

    # Step 1: Get current maximum error number
    max_id = 0
    id_pattern = re.compile(r'^E(\d+)$', re.IGNORECASE)  # Compatible with case
    for err in existing_errors:
        if match := id_pattern.match(err.get("error_id", "")):
            current_num = int(match.group(1))
            max_id = max(max_id, current_num)

    # Step 2: Assign new number
    for new_err in new_errors:
        # Check if there is a valid ID
        if "error_id" in new_err:
            if id_pattern.match(new_err["error_id"]):
                # Check if ID already exists
                existing_ids = {e["error_id"].upper() for e in existing_errors}
                if new_err["error_id"].upper() in existing_ids:
                    # ID conflict, automatically assign new number
                    max_id += 1
                    new_err["error_id"] = f"E{max_id:03d}"
                else:
                    # Update maximum ID (handle non-continuous cases)
                    if match := id_pattern.match(new_err["error_id"]):
                        current_num = int(match.group(1))
                        max_id = max(max_id, current_num)
            else:
                # Invalid format, automatically assign new number
                max_id += 1
                new_err["error_id"] = f"E{max_id:03d}"
        else:
            # Automatically assign new ID
            max_id += 1
            new_err["error_id"] = f"E{max_id:03d}"

    # Step 3: Append new data
    updated_errors = existing_errors + new_errors

    # Write back to file
    with open(error_data_file_path, 'w') as f:
        json.dump(updated_errors, f, indent=2, ensure_ascii=False)

def run_experiment3(failed_files, error_data_file_path, output_dir):
    prompt_file = os.path.join(exp3_prompt_folder_path, "prompt.txt")
    
    results_file = os.path.join(output_dir, "compilation_results.txt")
    log_file = os.path.join(output_dir, "experiment3.log")

    # Check if prompt file exists
    if not os.path.exists(prompt_file):
        raise FileNotFoundError("Required prompt file not found")
        
    # Read prompt file content
    with open(prompt_file, 'r') as f:
        prompt = f.read()

    # Initialize retriever
    retriever = ErrorRetriever(error_data_file_path)
    
    errors_map = {}

    # Modified main processing logic
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
        futures = []
        for file, error in failed_files:
            query = get_error_info(error)
            results = retriever.search(query, top_k=3)
            # Write results to log
            log_file = os.path.join(output_dir, "experiment3.log")
            with open(log_file, 'a') as f:
                f.write(f"Retrieval results example:\n{json.dumps(results, indent=2)}")

            # Get error information from retrieval results
            example_info = get_exp_prompt(results)

            future = executor.submit(
                process_single_file,
                file, error, output_dir, log_file, prompt, example_info
            )
            futures.append(future)
        
        # Wait for all tasks to complete
        for future in concurrent.futures.as_completed(futures):
            result, errors = future.result()
            if result:
                print(f"Successfully processed: {result}")
                errors_map[result] = errors


    fixed_files = [f for f in os.listdir(output_dir) if f.endswith('.tla')]
    still_failed = []
    failed_files = []

    for file in fixed_files:
        file_path = os.path.join(output_dir, file)

        add_var_func(file_path)
        # Run tla_sany
        result = tla_sany(file_path)
        # Check if there are compilation errors
        if "Error" not in result and "error" not in result:
            if UPDATE_ERROR:
                if file_path in errors_map:
                    update_errors_database(errors_map[file_path], error_data_file_path)
                else:
                    print(f"File {file_path} has been processed before")
            print(f"File {file} passed compilation")
        else:
            still_failed.append((file_path, result))
            failed_files.append((output_dir + "/" + file, result))
            with open(log_file, 'a') as f:
                f.write(f"File {file} still has compilation errors:\n{result}\n")
                
    # Record compilation result statistics
    with open(results_file, 'a') as f:
        f.write(f"Files passed compilation: {len(fixed_files) - len(still_failed)}\n")
        f.write(f"Files failed compilation: {len(still_failed)}\n\n")
        
        # Record files that passed compilation
        f.write("Files that passed compilation:\n")
        for file in fixed_files:
            if not any(file in failed[0] for failed in still_failed):
                f.write(f"- {file}\n")
        f.write("\n")
        
        # Record failed files and error information
        if still_failed:
            f.write("Failed files and error information:\n")
            for file, error in still_failed:
                f.write(f"=== {file} ===\n{error}\n\n")

    return failed_files

def run_all_experiments(code_folder_path, output_folder_path, error_data_file_path):
    # Create output directory
    exp1_dir, exp2_dir, exp3_dir = create_output_dirs(output_folder_path)
    # Clear log files
    with open(os.path.join(exp1_dir, "experiment1.log"), 'w') as f:
        f.write("")
    with open(os.path.join(exp2_dir, "experiment2.log"), 'w') as f:
        f.write("")
    with open(os.path.join(exp3_dir, "experiment3.log"), 'w') as f:
        f.write("")
    # Run experiment 1
    print("Starting experiment 1...")
    failed_files_2 = run_experiment1(code_folder_path, exp1_dir)
    failed_files_3 = failed_files_2
    # Run experiment 2
    # print("Starting experiment 2...")
    # for i in range(LOOPTIMES):
    #     failed_files_2 = run_experiment2(failed_files_2, exp2_dir)
    
    # Run experiment 3
    print("Starting experiment 3...")
    for i in range(LOOPTIMES):
        failed_files_3 = run_experiment3(failed_files_3, error_data_file_path, exp3_dir)

if __name__ == "__main__":
    args = parse_args()
    
    # Use parameters or default values
    error_data_file_path = args.error_data
    code_folder_path = args.code_folder
    output_folder_path = args.output_folder
    exp2_prompt_folder_path = args.exp2_prompt
    exp3_prompt_folder_path = args.exp3_prompt
    run_all_experiments(args.code_folder, args.output_folder, args.error_data)
