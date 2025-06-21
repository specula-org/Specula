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
            System.err.println("Usage: java -jar <jar_name>.jar <input_file.tla> <output_file.tla> [--show-tree]");
            System.err.println("       java -jar <jar_name>.jar --show-tree <input_file.tla> <output_file.tla>");
            System.exit(1); // Exit with error
        }

        // --- 2. Parse command line arguments ---
        // Support flexible argument order for --show-tree
        boolean showTree = false;
        String inputFile = null;
        String outputFile = null;
        
        // Parse arguments
        for (int i = 0; i < args.length; i++) {
            if (args[i].equalsIgnoreCase("--show-tree") || args[i].equalsIgnoreCase("-show-tree")) {
                showTree = true;
            } else if (inputFile == null) {
                inputFile = args[i];
            } else if (outputFile == null) {
                outputFile = args[i];
            }
        }
        
        // Validate that we have both input and output files
        if (inputFile == null || outputFile == null) {
            System.err.println("ERROR: Both input and output files must be specified.");
            System.err.println("Usage: java -jar <jar_name>.jar <input_file.tla> <output_file.tla> [--show-tree]");
            System.err.println("       java -jar <jar_name>.jar --show-tree <input_file.tla> <output_file.tla>");
            System.exit(1);
        }

        Path inputPath = Paths.get(inputFile);
        Path outputPath = Paths.get(outputFile);

        System.out.println("Processing input file: " + inputPath);
        if (showTree) {
            System.out.println("Parse tree GUI will be displayed");
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

        // --- 5. Core analysis logic (unchanged) ---
        CFGBuilderVisitor cfgBuilderVisitor = new CFGBuilderVisitor();
        cfgBuilderVisitor.visit(tree);  
        CFGGraphToStr cfgGraphToStr = new CFGGraphToStr();
        CFGCALLGraph callGraph = new CFGCALLGraph(cfgBuilderVisitor.getCfgFuncNodes(), cfgBuilderVisitor.getVariables(), cfgBuilderVisitor.getConstants());
        callGraph.buildCallGraph();
        CFGVarChangeAnalyzer cfgVarChangeAnalyzer = new CFGVarChangeAnalyzer(callGraph);
        cfgVarChangeAnalyzer.analyze();
        
        // --- 6. Get result string ---
        String resultString = cfgGraphToStr.CFGGraphToStr(cfgVarChangeAnalyzer.getCallGraph());

        // --- 7. Write result to file ---
        // Don't print to console, write to specified output file
        Files.writeString(outputPath, resultString);

        System.out.println("Processing finished. Output written to: " + outputPath);
    }
}