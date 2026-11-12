# Use other model providers with Codex

A `codex` profile in a [hybrid agent configuration](Usage.md#hybrid-agent-configuration) can run its phases on a model from another provider, for example to use a different model for bug confirmation.

1. Create a Codex config profile at `~/.codex/NAME.config.toml` (under `$CODEX_HOME` if you set it). The provider must support the OpenAI Responses API. Set `model_context_window` to the model's context size, because Codex has no built-in metadata for third-party models.

   ```toml
   model = "provider-model"
   model_provider = "provider"
   model_context_window = 200000

   [model_providers.provider]
   name = "Provider"
   base_url = "https://api.provider.example/v1"
   env_key = "PROVIDER_API_KEY"
   wire_api = "responses"
   ```

2. Name it with `codex_profile` in an agent configuration profile, and route phases to that profile:

   ```json
   "profiles": {
     "reproduction": {"agent": "codex", "model": "provider-model", "codex_profile": "NAME"}
   },
   "phases": {"confirm": "reproduction"}
   ```

3. Set the variable named by `env_key` before running Specula.

Specula stops before launching if the profile file does not exist. Individual phase commands take the same setting as `--agent=codex --codex-profile=NAME`.
