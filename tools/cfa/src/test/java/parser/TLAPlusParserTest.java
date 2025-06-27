package parser;

import java.util.Arrays;
import java.util.concurrent.CountDownLatch;

import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

import org.antlr.v4.gui.TreeViewer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.Test;

import CFG.CFGBuilderVisitor;
import CFG.CFGCALLGraph;
import CFG.CFGFuncNode;
import CFG.CFGVarChangeAnalyzer;
public class TLAPlusParserTest {
    
    @Test
    public void testBasicModule() throws Exception {
        // Test basic module definition
        String filePath = "src/test/java/parser/test.tla";
        String input = new String(java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(filePath)));
        
        // Create lexical analyzer
        CharStream stream = CharStreams.fromString(input);
        TLAPlusLexer lexer = new TLAPlusLexer(stream);
        
        // Create token stream
        CommonTokenStream tokens = new CommonTokenStream(lexer);
                                            
        // Print token stream
        tokens.fill();
        System.out.println("Tokens:");
        for (Token token : tokens.getTokens()) {
            System.out.printf("Token: %s ('%s')%n", 
                lexer.getVocabulary().getSymbolicName(token.getType()), 
                token.getText());
        }

        // Create syntax analyzer
        TLAPlusParser parser = new TLAPlusParser(tokens);
        System.out.println("Start parsing...");
        // Begin parsing
        ParseTree tree = parser.module();

        // Print syntax tree
        System.out.println(tree.toStringTree(parser));
        
        // Check if syntax tree display is needed
        String showTree = System.getProperty("showTree");
        if ("true".equalsIgnoreCase(showTree)) {
            // Visualize syntax tree
            JFrame frame = new JFrame("ANTLR Parse Tree");
            JPanel panel = new JPanel();
            TreeViewer viewer = new TreeViewer(Arrays.asList(parser.getRuleNames()), tree);
            viewer.setScale(1.5); // Scale to fit window
            panel.add(viewer);

            // Put TreeViewer into JScrollPane
            JScrollPane scrollPane = new JScrollPane(panel);
            frame.add(scrollPane);
            frame.setSize(800, 600);

            // Use CountDownLatch to wait for window closure
            CountDownLatch latch = new CountDownLatch(1);
            frame.addWindowListener(new java.awt.event.WindowAdapter() {
                @Override
                public void windowClosing(java.awt.event.WindowEvent windowEvent) {
                    latch.countDown(); // Decrease count when window closes
                }
            });

            frame.setVisible(true);
            System.out.println("Parsing finished.");

            // Wait for window closure
            latch.await();
        }

        CFGBuilderVisitor cfgBuilderVisitor = new CFGBuilderVisitor();
        cfgBuilderVisitor.visit(tree);
        for (CFGFuncNode funcNode : cfgBuilderVisitor.getCfgFuncNodes()) {
            funcNode.printSingleFunc();
        }
        CFGCALLGraph callGraph = new CFGCALLGraph(cfgBuilderVisitor.getCfgFuncNodes(), cfgBuilderVisitor.getVariables(), cfgBuilderVisitor.getConstants());
        callGraph.buildCallGraph();
        CFGVarChangeAnalyzer varChangeAnalyzer = new CFGVarChangeAnalyzer(callGraph);
        varChangeAnalyzer.analyze();
        // Verify if parsing is successful
        assert(parser.getNumberOfSyntaxErrors() == 0);
    }
}
