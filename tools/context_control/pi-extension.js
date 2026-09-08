import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

export default function (pi) {
  if (process.env.SPECULA_PHASE !== "incremental" || !process.env.SPECULA_CONTEXT_REQUEST) return;
  pi.registerTool({
    name: "request_context_compaction",
    label: "Request context compaction",
    description: "After saving a Markdown handoff and collecting outstanding tool results, request compaction of this CI conversation. Follow the returned yield instructions; this is not CI completion.",
    parameters: {
      type: "object",
      properties: { handoff_path: { type: "string" } },
      required: ["handoff_path"],
      additionalProperties: false,
    },
    async execute(_id, params) {
      const output = execFileSync(process.env.SPECULA_CONTEXT_PYTHON, [
        fileURLToPath(new URL("request.py", import.meta.url)), params.handoff_path,
      ], { encoding: "utf8" });
      return { content: [{ type: "text", text: output }], details: {} };
    },
  });
}
