import { execFile } from "node:child_process";
import { fileURLToPath } from "node:url";

export default function (pi) {
  const python = process.env.SPECULA_TLC_TOOL_PYTHON;
  if (!python) return;
  const script = fileURLToPath(new URL("../../src/specula/tlc_tasks.py", import.meta.url));
  const definitions = [
    {
      name: "start_tlc",
      description: "Start resource-budgeted TLC model checking or simulation. Prefer this over shell java commands. Pass work_dir, spec_file, config_file and wrapper options: -m heap, -M offheap, -w workers, -t minutes; -S -n traces -p depth for simulation. Follow the returned waiting instructions.",
      properties: {
        work_dir: { type: "string" }, spec_file: { type: "string" }, config_file: { type: "string" },
        options: { type: "array", items: { type: "string" } },
      },
      required: ["work_dir", "spec_file", "config_file"],
    },
    {
      name: "wait_tlc",
      description: "Wait inside the tool for TLC tasks, without repeated shell/log polling. Default: up to one hour, returning when any task finishes. Timeout/cancellation stops only waiting, not TLC. Reuse the same task IDs. Process exit is not a verification verdict; inspect evidence.",
      properties: {
        task_ids: { type: "array", items: { type: "string" }, minItems: 1 },
        timeout_seconds: { type: "integer", minimum: 0, maximum: 3600 },
        mode: { type: "string", enum: ["any", "all"] },
      },
      required: ["task_ids"],
    },
  ];
  for (const definition of definitions) {
    pi.registerTool({
      name: definition.name,
      label: definition.name,
      description: definition.description,
      parameters: { type: "object", properties: definition.properties, required: definition.required, additionalProperties: false },
      async execute(_id, params, signal) {
        const output = await new Promise((resolve, reject) => {
          execFile(python, [script, definition.name, JSON.stringify(params)], { signal, encoding: "utf8" }, (error, stdout) => {
            if (error) reject(error);
            else resolve(stdout);
          });
        });
        return { content: [{ type: "text", text: output }], details: {} };
      },
    });
  }
}
