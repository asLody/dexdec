import { invoke } from "@tauri-apps/api/core";

export interface McpConfiguration {
  command: string;
  args: string[];
}

export interface McpConfigurationDocument extends McpConfiguration {
  json: string;
}

export interface AgentMcpIntegration {
  id: string;
  name: string;
  available: boolean;
  configured: boolean;
  needsUpdate: boolean;
  configPath: string;
  message: string | null;
}

export class McpConfigurationClient {
  async configuration(): Promise<McpConfigurationDocument> {
    const configuration = await invoke<McpConfiguration>("mcp_configuration");
    const json = JSON.stringify(
      {
        mcpServers: {
          dexdec: {
            command: configuration.command,
            args: configuration.args,
          },
        },
      },
      null,
      2,
    );
    return { ...configuration, json };
  }

  integrations(): Promise<AgentMcpIntegration[]> {
    return invoke<AgentMcpIntegration[]>("mcp_agent_integrations");
  }

  configureAgent(agentId: string): Promise<AgentMcpIntegration> {
    return invoke<AgentMcpIntegration>("configure_mcp_agent", {
      agentId,
    });
  }

  unconfigureAgent(agentId: string): Promise<AgentMcpIntegration> {
    return invoke<AgentMcpIntegration>("unconfigure_mcp_agent", {
      agentId,
    });
  }

  configureAll(): Promise<AgentMcpIntegration[]> {
    return invoke<AgentMcpIntegration[]>("configure_all_mcp_agents");
  }
}

export const mcpConfigurationClient = new McpConfigurationClient();
