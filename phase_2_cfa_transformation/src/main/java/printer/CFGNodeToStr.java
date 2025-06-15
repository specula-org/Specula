package printer;
import CFG.CFGStmtNode;

public class CFGNodeToStr {
    public static String CFGStmtNodeToStr(CFGStmtNode node) {
        if (node == null) return "";
        switch (node.getType()) {
            case NORMAL:
                return NORMALCFGStmtNodeToStr(node);
            case IF_ELSE:
                return IF_ELSECFGStmtNodeToStr(node);
            case CALL:
                return CALLCFGStmtNodeToStr(node);
            case ROOT:
                return ROOTCFGStmtNodeToStr(node);
            case SKIP:
                return SKIPCFGStmtNodeToStr(node);
            case LET: 
                return LETCFGStmtNodeToStr(node);
            default:
                System.err.println("不支持的语句类型: " + node.getType());
                return "";
        }
    }

    private static String NORMALCFGStmtNodeToStr(CFGStmtNode node){
        return node.getContent();
    }

    private static String IF_ELSECFGStmtNodeToStr(CFGStmtNode node){
        return node.getContent();
    }

    private static String CALLCFGStmtNodeToStr(CFGStmtNode node){
        return node.getContent();
    }   

    private static String LETCFGStmtNodeToStr(CFGStmtNode node){
        return node.getContent();
    }

    private static String ROOTCFGStmtNodeToStr(CFGStmtNode node){
        return "";
    }

    private static String SKIPCFGStmtNodeToStr(CFGStmtNode node){
        return "";
    }
}
