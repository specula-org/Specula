// 将 'parser' 替换成你自己的包名
package parser;

// --- 所有需要的 import 语句 ---
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
// --- 导入你自己的类 ---
import CFG.CFGBuilderVisitor;
import CFG.CFGCALLGraph;
import CFG.CFGVarChangeAnalyzer;
import printer.CFGGraphToStr;
// ... 可能还有其他 ...


public class CfaTransformerCli {

    public static void main(String[] args) throws Exception { // main 方法可以抛出 Exception

        // --- 1. 参数校验 ---
        // 我们期望至少两个参数：输入文件和输出文件
        if (args.length < 2) {
            System.err.println("ERROR: Missing arguments.");
            System.err.println("Usage: java -jar <jar_name>.jar <input_file.tla> <output_file.tla> [--show-tree]");
            System.exit(1); // 异常退出
        }

        // --- 2. 从命令行参数获取输入和输出路径 ---
        // 【修改点 1】: 不再硬编码，而是从 args 数组获取
        Path inputPath = Paths.get(args[0]);
        Path outputPath = Paths.get(args[1]);

        // 【修改点 2】: 从命令行参数处理可选配置
        boolean showTree = false;
        if (args.length > 2 && args[2].equalsIgnoreCase("--show-tree")) {
            showTree = true;
        }

        System.out.println("Processing input file: " + inputPath);

        // --- 3. 这是你从测试文件中复制过来的核心逻辑 ---
        String input = new String(Files.readAllBytes(inputPath));
        
        // 创建词法分析器
        CharStream stream = CharStreams.fromString(input);
        TLAPlusLexer lexer = new TLAPlusLexer(stream);
        
        // 创建词符流
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // 创建语法分析器
        TLAPlusParser parser = new TLAPlusParser(tokens);
        System.out.println("Start parsing...");
        ParseTree tree = parser.module(); // 开始解析

        // 【修改点 3】: 使用我们从参数解析出的布尔变量
        if (showTree) {
            System.out.println("Displaying parse tree GUI...");
            // 注意：GUI部分可能会让命令行工具挂起，直到窗口关闭。
            // 这是一个高级问题，但对于 artifact 来说，可以暂时接受。
            // 你的 CountDownLatch 逻辑在这里可能需要调整以避免程序提前退出。
            // 一个简单的处理方式是在这里显示GUI，并让用户手动关闭它。
            JFrame frame = new JFrame("ANTLR Parse Tree");
            JPanel panel = new JPanel();
            TreeViewer viewer = new TreeViewer(Arrays.asList(parser.getRuleNames()), tree);
            viewer.setScale(1.5);
            panel.add(viewer);
            JScrollPane scrollPane = new JScrollPane(panel);
            frame.add(scrollPane);
            frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE); // 关闭窗口时释放资源
            frame.pack();
            frame.setSize(800, 600);
            frame.setVisible(true);
        }

        // --- 4. 你的核心分析逻辑 (完全不变) ---
        CFGBuilderVisitor cfgBuilderVisitor = new CFGBuilderVisitor();
        cfgBuilderVisitor.visit(tree);  
        CFGGraphToStr cfgGraphToStr = new CFGGraphToStr();
        CFGCALLGraph callGraph = new CFGCALLGraph(cfgBuilderVisitor.getCfgFuncNodes(), cfgBuilderVisitor.getVariables(), cfgBuilderVisitor.getConstants());
        callGraph.buildCallGraph();
        CFGVarChangeAnalyzer cfgVarChangeAnalyzer = new CFGVarChangeAnalyzer(callGraph);
        cfgVarChangeAnalyzer.analyze();
        
        // --- 5. 获取结果字符串 ---
        String resultString = cfgGraphToStr.CFGGraphToStr(cfgVarChangeAnalyzer.getCallGraph());

        // --- 6. 将结果写入文件 ---
        // 【修改点 4】: 不再打印到控制台，而是写入到指定的输出文件
        Files.writeString(outputPath, resultString);

        System.out.println("Processing finished. Output written to: " + outputPath);
    }
}