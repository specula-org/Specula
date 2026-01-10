import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import CFG.SANYCFGBuilder;

/**
 * Real CFG test: input spec -> build CFG -> print structure
 */
public class RealCFGTest {
    
    public static void main(String[] args) {
        System.out.println("=================================");
        System.out.println("   Control Flow Graph (CFG)");
        System.out.println("=================================");
        System.out.println();

        // Get default path relative to project structure
        String speculaRoot = System.getenv("SPECULA_ROOT");
        String defaultPath;
        if (speculaRoot != null && !speculaRoot.isEmpty()) {
            defaultPath = speculaRoot + "/tools/cfa/input/test/SimpleCounter.tla";
        } else {
            // Assume running from project root or tools/cfa directory
            defaultPath = "tools/cfa/input/test/SimpleCounter.tla";
        }
        String fileName = args.length > 0 ? args[0] : defaultPath;
        
        try {
            // Step 1: Input spec
            System.out.println("1. Parsing TLA+ file: " + fileName);
            SpecObj spec = new SpecObj(fileName);
            
            // Parse the spec
            SANY.frontEndMain(spec, fileName, System.out);
            
            if (spec.getErrorLevel() > 0) {
                System.err.println("Parse errors occurred");
                return;
            }
            
            // Step 2: Build CFG  
            System.out.println("2. Building CFG...");
            SANYCFGBuilder builder = new SANYCFGBuilder();
            
            ModuleNode rootModule = spec.getRootModule();
            if (rootModule != null) {
                // Use the semantic tree, not parse tree
                String sourceText = Files.readString(Paths.get(fileName));
                builder.buildCFG(rootModule, sourceText);
            }
            
            // Step 3: Print structure
            System.out.println("3. CFG Structure:");
            System.out.println();
            if (builder.getCfgFuncNodes().isEmpty()) {
                System.out.println("No CFG functions built");
            } else {
                for (int i = 0; i < builder.getCfgFuncNodes().size(); i++) {
                    System.out.println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
                    System.out.println("Function: " + builder.getCfgFuncNodes().get(i).getFuncName());
                    System.out.println("Parameters: " + builder.getCfgFuncNodes().get(i).getParameters());
                    System.out.println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
                    System.out.println();
                    System.out.println(builder.getCfgFuncNodes().get(i).getRoot().printTree());
                    System.out.println();
                }
            }
            
        } catch (Exception e) {
            System.err.println("ERROR: " + e.getMessage());
            e.printStackTrace();
        }
    }
}
