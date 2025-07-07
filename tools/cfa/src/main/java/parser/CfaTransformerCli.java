// Replace 'parser' with your own package name
package parser;

// --- All required import statements ---
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import org.antlr.v4.gui.TreeViewer;
// --- Import your own classes ---
import CFG.CFGBuilderVisitor;
import CFG.CFGCALLGraph;
import CFG.CFGVarChangeAnalyzer;
import printer.CFGGraphToStr;
// ... possibly others ...


public class CfaTransformerCli {

    public static void main(String[] args) throws Exception { // main method can throw Exception

        // --- 1. Argument Validation ---
        // We expect at least two arguments: input file and output file
        if (args.length < 2) {
            System.err.println("ERROR: Missing arguments.");
            System.err.println("Usage: java -jar <jar_name>.jar <input_file.tla> <output_file.tla> [--show-tree] [--algorithm <algorithm>] [--debug]");
            System.err.println("       java -jar <jar_name>.jar --show-tree <input_file.tla> <output_file.tla>");
            System.err.println("       java -jar <jar_name>.jar --algorithm sa <input_file.tla> <output_file.tla>");
            System.err.println("       java -jar <jar_name>.jar --algorithm pc <input_file.tla> <output_file.tla>");
            System.err.println("       java -jar <jar_name>.jar --debug <input_file.tla> <output_file.tla>");
            System.err.println("");
            System.err.println("Algorithm options:");
            System.err.println("  --algorithm all    Run all algorithms (default)");
            System.err.println("  --algorithm sa     Run static analysis only");
            System.err.println("  --algorithm uc     Run unchanged variable analysis only");
            System.err.println("  --algorithm ud     Run undefined variable analysis only");
            System.err.println("  --algorithm pc     Run process cutting analysis only");
            System.err.println("");
            System.err.println("Debug options:");
            System.err.println("  --debug            Print IN/OUT variables for each statement (for debugging)");
            System.exit(1); // Exit with error
        }

        // --- 2. Parse command line arguments ---
        // Support flexible argument order for --show-tree and --algorithm
        boolean showTree = false;
        boolean debugMode = false;
        String algorithm = "all"; // Default to running all algorithms
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
        if (!algorithm.equals("all") && !algorithm.equals("sa") && !algorithm.equals("uc") && !algorithm.equals("ud") && !algorithm.equals("pc")) {
            System.err.println("ERROR: Invalid algorithm: " + algorithm);
            System.err.println("Valid algorithms: all, sa, uc, ud, pc");
            System.exit(1);
        }
        
        // Validate that we have both input and output files
        if (inputFile == null || outputFile == null) {
            System.err.println("ERROR: Both input and output files must be specified.");
            System.err.println("Usage: java -jar <jar_name>.jar <input_file.tla> <output_file.tla> [--show-tree] [--algorithm <algorithm>] [--debug]");
            System.err.println("       java -jar <jar_name>.jar --show-tree <input_file.tla> <output_file.tla>");
            System.err.println("       java -jar <jar_name>.jar --algorithm sa <input_file.tla> <output_file.tla>");
            System.exit(1);
        }

        Path inputPath = Paths.get(inputFile);
        Path outputPath = Paths.get(outputFile);

        System.out.println("Processing input file: " + inputPath);
        if (showTree) {
            System.out.println("Parse tree GUI will be displayed");
        }
        if (debugMode) {
            System.out.println("Debug mode enabled: IN/OUT variables will be printed");
        }

        // --- 3. Core logic copied from test file ---
        String input = new String(Files.readAllBytes(inputPath));
        
        // Create lexer
        CharStream stream = CharStreams.fromString(input);
        TLAPlusLexer lexer = new TLAPlusLexer(stream);
        
        // Create token stream
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // Create parser
        TLAPlusParser parser = new TLAPlusParser(tokens);
        System.out.println("Start parsing...");
        ParseTree tree = parser.module(); // Start parsing

        // --- 4. Display parse tree if requested ---
        if (showTree) {
            System.out.println("Displaying parse tree GUI...");
            // Note: GUI part may cause command line tool to hang until window is closed.
            // This is an advanced issue, but acceptable for artifact purposes.
            // A simple approach is to display GUI here and let user manually close it.
            JFrame frame = new JFrame("ANTLR Parse Tree");
            JPanel panel = new JPanel();
            TreeViewer viewer = new TreeViewer(Arrays.asList(parser.getRuleNames()), tree);
            viewer.setScale(1.5);
            panel.add(viewer);
            JScrollPane scrollPane = new JScrollPane(panel);
            frame.add(scrollPane);
            frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE); // Release resources when window is closed
            frame.pack();
            frame.setSize(800, 600);
            frame.setVisible(true);
            
            // Wait for user to close the window before continuing
            System.out.println("Close the parse tree window to continue processing...");
            while (frame.isVisible()) {
                Thread.sleep(100);
            }
        }

        // --- 5. Core analysis logic ---
        CFGBuilderVisitor cfgBuilderVisitor = new CFGBuilderVisitor();
        cfgBuilderVisitor.visit(tree);  
        CFGGraphToStr cfgGraphToStr = new CFGGraphToStr();
        CFGCALLGraph callGraph = new CFGCALLGraph(cfgBuilderVisitor.getCfgFuncNodes(), cfgBuilderVisitor.getVariables(), cfgBuilderVisitor.getConstants());
        callGraph.buildCallGraph(debugMode);
        CFGVarChangeAnalyzer cfgVarChangeAnalyzer = new CFGVarChangeAnalyzer(callGraph);
        
        // Run selected algorithm(s)
        System.out.println("Running algorithm: " + algorithm);
        switch (algorithm) {
            case "all":
                System.out.println("Running all algorithms (SA + UC + UD)...");
                cfgVarChangeAnalyzer.analyze();
                break;
            case "sa":
                System.out.println("Running static analysis only...");
                cfgVarChangeAnalyzer.analyze_only_sa();
                break;
            case "uc":
                System.out.println("Running unchanged variable analysis only...");
                cfgVarChangeAnalyzer.analyze_only_uc();
                break;
            case "ud":
                System.out.println("Running undefined variable analysis only...");
                cfgVarChangeAnalyzer.analyze_only_ud();
                break;
            case "pc":
                System.out.println("Running process cutting analysis only...");
                cfgVarChangeAnalyzer.analyze_only_pc();
                break;
            default:
                System.err.println("ERROR: Unknown algorithm: " + algorithm);
                System.exit(1);
        }
        
        // --- Print debug information if requested ---
        if (debugMode) {
            System.out.println("\n=== DEBUG MODE: Printing debug information ===");
            cfgVarChangeAnalyzer.printInOutVars();
            cfgVarChangeAnalyzer.printFuncVarChange();
            cfgVarChangeAnalyzer.printCuttedFuncInfo();
        }
        
        // --- 6. Get result string ---
        String resultString = cfgGraphToStr.CFGGraphToStr(cfgVarChangeAnalyzer.getCallGraph());

        // --- 7. Write result to file ---
        // Don't print to console, write to specified output file
        Files.writeString(outputPath, resultString);

        System.out.println("Processing finished. Output written to: " + outputPath);
    }
}