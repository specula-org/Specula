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
        // 测试基本的模块定义
        String filePath = "src/test/java/parser/etcd.tla";
        String input = new String(java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(filePath)));
        
        // 创建词法分析器
        CharStream stream = CharStreams.fromString(input);
        TLAPlusLexer lexer = new TLAPlusLexer(stream);
        
        // 创建词符流
        CommonTokenStream tokens = new CommonTokenStream(lexer);
                                            
        //打印词符流
        // import org.antlr.v4.runtime.Token;
        // tokens.fill();
        // System.out.println("Tokens:");
        // for (Token token : tokens.getTokens()) {
        //     System.out.printf("Token: %s ('%s')%n", 
        //         lexer.getVocabulary().getSymbolicName(token.getType()), 
        //         token.getText());
        // }

        // 创建语法分析器
        TLAPlusParser parser = new TLAPlusParser(tokens);
        System.out.println("Start parsing...");
        // 开始解析
        ParseTree tree = parser.module();

        // 打印语法树
        // System.out.println(tree.toStringTree(parser));
        
        // 检查是否需要显示语法树
        String showTree = System.getProperty("showTree");
        if ("true".equalsIgnoreCase(showTree)) {
            // 可视化语法树
            JFrame frame = new JFrame("ANTLR Parse Tree");
            JPanel panel = new JPanel();
            TreeViewer viewer = new TreeViewer(Arrays.asList(parser.getRuleNames()), tree);
            viewer.setScale(1.5); // 缩放以适应窗口
            panel.add(viewer);

            // 将 TreeViewer 放入 JScrollPane 中
            JScrollPane scrollPane = new JScrollPane(panel);
            frame.add(scrollPane);
            frame.setSize(800, 600);

            // 使用 CountDownLatch 等待窗口关闭
            CountDownLatch latch = new CountDownLatch(1);
            frame.addWindowListener(new java.awt.event.WindowAdapter() {
                @Override
                public void windowClosing(java.awt.event.WindowEvent windowEvent) {
                    latch.countDown(); // 窗口关闭时减少计数
                }
            });

            frame.setVisible(true);
            System.out.println("Parsing finished.");

            // 等待窗口关闭
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
