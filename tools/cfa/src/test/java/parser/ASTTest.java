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
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.Test;

import CFG.CFGBuilderVisitor;
import CFG.CFGCALLGraph;
import CFG.CFGVarChangeAnalyzer;
import printer.CFGGraphToStr;

public class ASTTest {
    @Test
    public void testBasicModule() throws Exception{
        // Test basic module definition
        String filePath = "src/test/java/parser/etcd.tla";
        String input = new String(java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(filePath)));
        
        // Create lexer
        CharStream stream = CharStreams.fromString(input);
        TLAPlusLexer lexer = new TLAPlusLexer(stream);
        
        // Create token stream
        CommonTokenStream tokens = new CommonTokenStream(lexer);
                                            
        // Print token stream
        // import org.antlr.v4.runtime.Token;
        // tokens.fill();
        // System.out.println("Tokens:");
        // for (Token token : tokens.getTokens()) {
        //     System.out.printf("Token: %s ('%s')%n", 
        //         lexer.getVocabulary().getSymbolicName(token.getType()), 
        //         token.getText());
        // }

        // Create parser
        TLAPlusParser parser = new TLAPlusParser(tokens);
        System.out.println("Start parsing...");
        // Start parsing
        ParseTree tree = parser.module();

        // Print syntax tree
        // System.out.println(tree.toStringTree(parser));
        
        // Check if need to show syntax tree
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

            // Use CountDownLatch to wait for window to close
            CountDownLatch latch = new CountDownLatch(1);
            frame.addWindowListener(new java.awt.event.WindowAdapter() {
                @Override
                public void windowClosing(java.awt.event.WindowEvent windowEvent) {
                    latch.countDown(); // Reduce count when window is closed
                }
            });

            frame.setVisible(true);
            System.out.println("Parsing finished.");

            // Wait for window to close
            latch.await();
        }
        CFGBuilderVisitor cfgBuilderVisitor = new CFGBuilderVisitor();
        cfgBuilderVisitor.visit(tree);  
        CFGGraphToStr cfgGraphToStr = new CFGGraphToStr();
        CFGCALLGraph callGraph = new CFGCALLGraph(cfgBuilderVisitor.getCfgFuncNodes(), cfgBuilderVisitor.getVariables(), cfgBuilderVisitor.getConstants());
        callGraph.buildCallGraph();
        CFGVarChangeAnalyzer cfgVarChangeAnalyzer = new CFGVarChangeAnalyzer(callGraph);
        cfgVarChangeAnalyzer.analyze();
        System.out.println(cfgGraphToStr.CFGGraphToStr(cfgVarChangeAnalyzer.getCallGraph()));
    }
}
