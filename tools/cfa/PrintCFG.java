import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import CFG.SANYCFGBuilder;
import CFG.CFGFuncNode;

/**
 * Print CFG tree structure for a TLA+ specification
 */
public class PrintCFG {

    public static void main(String[] args) {
        if (args.length < 1) {
            System.err.println("Usage: java PrintCFG <input_file.tla>");
            System.exit(1);
        }

        String fileName = args[0];

        System.out.println("=================================");
        System.out.println("   Control Flow Graph (CFG)");
        System.out.println("=================================");
        System.out.println();

        try {
            // Step 1: Parse TLA+ file
            System.out.println("Parsing TLA+ file: " + fileName);
            SpecObj spec = new SpecObj(fileName);

            SANY.frontEndMain(spec, fileName, new PrintStream(new ByteArrayOutputStream()));

            if (spec.getErrorLevel() > 0) {
                System.err.println("Parse errors occurred");
                return;
            }

            // Step 2: Build CFG
            System.out.println("Building CFG...");
            SANYCFGBuilder builder = new SANYCFGBuilder();

            ModuleNode rootModule = spec.getRootModule();
            if (rootModule != null) {
                String sourceText = Files.readString(Paths.get(fileName));
                builder.buildCFG(rootModule, sourceText);
            }

            System.out.println("✓ CFG built successfully!");
            System.out.println();

            // Step 3: Print CFG tree structure
            if (builder.getCfgFuncNodes().isEmpty()) {
                System.out.println("No CFG functions built");
            } else {
                for (CFGFuncNode funcNode : builder.getCfgFuncNodes()) {
                    System.out.println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
                    System.out.println("Function: " + funcNode.getFuncName());
                    System.out.println("Parameters: " + funcNode.getParameters());
                    System.out.println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
                    System.out.println();
                    System.out.println(funcNode.getRoot().printTree());
                    System.out.println();
                }
            }

        } catch (Exception e) {
            System.err.println("ERROR: " + e.getMessage());
            e.printStackTrace();
        }
    }
}
