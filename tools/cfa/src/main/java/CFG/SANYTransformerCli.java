package CFG;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import printer.CFGFuncToStr;

/**
 * SANY-based Control Flow Analysis Transformer CLI
 * Replaces the old ANTLR-based CfaTransformerCli with SANY parser integration
 */
public class SANYTransformerCli {
    
    public static void main(String[] args) throws Exception {
        
        // --- 1. Argument Validation ---
        if (args.length < 2) {
            System.err.println("ERROR: Missing arguments.");
            System.err.println("Usage: java -jar <jar_name>.jar <input_file.tla> <output_file.tla> [--show-tree] [--algorithm <algorithm>] [--debug]");
            System.err.println("       java -jar <jar_name>.jar --show-tree <input_file.tla> <output_file.tla>");
            System.err.println("       java -jar <jar_name>.jar --algorithm sa <input_file.tla> <output_file.tla>");
            System.err.println("");
            System.err.println("Algorithm options:");
            System.err.println("  --algorithm all    Run all algorithms (default)");
            System.err.println("  --algorithm cfg    Build CFG only");
            System.err.println("  --algorithm print  Build CFG and print formatted TLA+");
            System.err.println("");
            System.err.println("Debug options:");
            System.err.println("  --debug            Print detailed parsing information");
            System.err.println("  --show-tree        Show SANY AST information");
            System.exit(1);
        }
        
        // --- 2. Parse command line arguments ---
        boolean showTree = false;
        boolean debugMode = false;
        String algorithm = "print"; // Default to CFG + print
        String inputFile = null;
        String outputFile = null;
        
        // Parse arguments
        for (int i = 0; i < args.length; i++) {
            if (args[i].equalsIgnoreCase("--show-tree") || args[i].equalsIgnoreCase("-show-tree")) {
                showTree = true;
            } else if (args[i].equalsIgnoreCase("--debug") || args[i].equalsIgnoreCase("-debug")) {
                debugMode = true;
            } else if (args[i].equalsIgnoreCase("--algorithm") || args[i].equalsIgnoreCase("-algorithm")) {
                if (i + 1 < args.length) {
                    algorithm = args[i + 1].toLowerCase();
                    i++; // Skip the next argument since we've consumed it
                } else {
                    System.err.println("ERROR: --algorithm requires a value");
                    System.exit(1);
                }
            } else if (inputFile == null) {
                inputFile = args[i];
            } else if (outputFile == null) {
                outputFile = args[i];
            }
        }
        
        // Validate algorithm parameter
        if (!algorithm.equals("all") && !algorithm.equals("cfg") && !algorithm.equals("print")) {
            System.err.println("ERROR: Invalid algorithm: " + algorithm);
            System.err.println("Valid algorithms: all, cfg, print");
            System.exit(1);
        }
        
        // Validate that we have both input and output files
        if (inputFile == null || outputFile == null) {
            System.err.println("ERROR: Both input and output files must be specified.");
            System.err.println("Usage: java -jar <jar_name>.jar <input_file.tla> <output_file.tla> [options]");
            System.exit(1);
        }
        
        Path inputPath = Paths.get(inputFile);
        Path outputPath = Paths.get(outputFile);
        
        System.out.println("Processing input file: " + inputPath);
        if (showTree) {
            System.out.println("SANY AST information will be displayed");
        }
        if (debugMode) {
            System.out.println("Debug mode enabled: detailed parsing information will be printed");
        }
        
        // --- 3. SANY Parsing ---
        System.out.println("Parsing TLA+ file with SANY...");
        
        // Create SpecObj and parse
        SpecObj spec = new SpecObj(inputFile);
        
        // Capture SANY output if debug mode  
        PrintStream sanyOutput = debugMode ? System.out : new PrintStream(new ByteArrayOutputStream());
        
        try {
            SANY.frontEndMain(spec, inputFile, sanyOutput);
            sanyOutput.flush();
            
            if (spec.getErrorLevel() > 0) {
                System.err.println("SANY parsing failed with errors:");
                System.err.println("Error level: " + spec.getErrorLevel());
                if (spec.getParseErrors() != null) {
                    System.err.println("Parse errors: " + spec.getParseErrors().toString());
                }
                if (spec.getSemanticErrors() != null) {
                    System.err.println("Semantic errors: " + spec.getSemanticErrors().toString());
                }
                System.exit(1);
            }
            
            System.out.println("✅ SANY parsing successful!");
            
        } catch (Exception e) {
            System.err.println("ERROR: SANY parsing failed: " + e.getMessage());
            if (debugMode) {
                e.printStackTrace();
            }
            System.exit(1);
        }
        
        // --- 4. Display SANY AST information if requested ---
        if (showTree) {
            System.out.println("\n=== SANY AST INFORMATION ===");
            ModuleNode rootModule = spec.getRootModule();
            if (rootModule != null) {
                System.out.println("Module name: " + rootModule.getName());
                System.out.println("Module location: " + rootModule.getLocation());
                System.out.println("Tree node: " + rootModule.getTreeNode());
            } else {
                System.out.println("No root module found");
            }
            System.out.println("=== END SANY AST INFORMATION ===\n");
        }
        
        // --- 5. CFG Building ---
        System.out.println("Building CFG with SANYCFGBuilder...");
        
        SANYCFGBuilder cfgBuilder = new SANYCFGBuilder();
        
        try {
            ModuleNode rootModule = spec.getRootModule();
            if (rootModule != null) {
                // Build CFG from SANY AST
                cfgBuilder.buildCFG(rootModule.getTreeNode());
                
                System.out.println("✅ CFG building successful!");
                System.out.println("Found " + cfgBuilder.getCfgFuncNodes().size() + " operators");
                System.out.println("Found " + cfgBuilder.getVariables().size() + " variables");
                System.out.println("Found " + cfgBuilder.getConstants().size() + " constants");
                
                if (debugMode) {
                    System.out.println("\nVariables: " + cfgBuilder.getVariables());
                    System.out.println("Constants: " + cfgBuilder.getConstants());
                    System.out.println("Operators: ");
                    for (CFGFuncNode func : cfgBuilder.getCfgFuncNodes()) {
                        System.out.println("  - " + func.getFuncName() + "(" + String.join(", ", func.getParameters()) + ")");
                    }
                }
                
            } else {
                System.err.println("ERROR: No root module found in parsed spec");
                System.exit(1);
            }
            
        } catch (Exception e) {
            System.err.println("ERROR: CFG building failed: " + e.getMessage());
            if (debugMode) {
                e.printStackTrace();
            }
            System.exit(1);
        }
        
        // --- 6. Run selected algorithm ---
        String resultString = "";
        
        System.out.println("Running algorithm: " + algorithm);
        switch (algorithm) {
            case "cfg":
                System.out.println("CFG building completed. No output generated.");
                resultString = "% CFG building completed successfully\n% " + cfgBuilder.getCfgFuncNodes().size() + " operators processed\n";
                break;
                
            case "print":
                System.out.println("Building formatted TLA+ output...");
                resultString = buildFormattedOutput(cfgBuilder, debugMode);
                break;
                
            case "all":
                System.out.println("Running full analysis (CFG + formatting)...");
                resultString = buildFormattedOutput(cfgBuilder, debugMode);
                // TODO: Add more analysis algorithms here when implemented
                break;
                
            default:
                System.err.println("ERROR: Unknown algorithm: " + algorithm);
                System.exit(1);
        }
        
        // --- 7. Write result to file ---
        try {
            Files.writeString(outputPath, resultString);
            System.out.println("✅ Processing finished. Output written to: " + outputPath);
            
        } catch (IOException e) {
            System.err.println("ERROR: Failed to write output file: " + e.getMessage());
            System.exit(1);
        }
    }
    
    /**
     * Build formatted TLA+ output from CFG
     */
    private static String buildFormattedOutput(SANYCFGBuilder cfgBuilder, boolean debugMode) {
        StringBuilder result = new StringBuilder();
        
        // Add header comment
        result.append("\\* Generated by SANY CFG Transformer\n");
        result.append("\\* Original operators reconstructed from Control Flow Graph\n\n");
        
        // Process each function
        CFGFuncToStr funcToStr = new CFGFuncToStr();
        
        for (CFGFuncNode funcNode : cfgBuilder.getCfgFuncNodes()) {
            if (debugMode) {
                System.out.println("Processing function: " + funcNode.getFuncName());
            }
            
            try {
                List<String> funcLines = funcToStr.CFGFuncToStr(funcNode);
                
                // Add function to result
                for (String line : funcLines) {
                    result.append(line).append("\n");
                }
                result.append("\n"); // Add blank line between functions
                
            } catch (Exception e) {
                System.err.println("WARNING: Failed to process function " + funcNode.getFuncName() + ": " + e.getMessage());
                if (debugMode) {
                    e.printStackTrace();
                }
            }
        }
        
        // Add footer
        result.append("\\* End of generated TLA+ specification\n");
        
        return result.toString();
    }
}