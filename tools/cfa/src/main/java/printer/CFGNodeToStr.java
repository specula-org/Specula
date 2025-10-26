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
            case UNCHANGED:
                return UNCHANGEDCFGStmtNodeToStr(node);
            case CASE:
                return CASECFGStmtNodeToStr(node);
            case CASE_ARM:
                return CASE_ARMCFGStmtNodeToStr(node);
            case DISJUNCTION:
                return DISJUNCTIONCFGStmtNodeToStr(node);
            case CHOOSE:
                return CHOOSECFGStmtNodeToStr(node);
            case EXISTS:
                return EXISTSCFGStmtNodeToStr(node);
            case FORALL:
                return FORALLCFGStmtNodeToStr(node);
            default:
                System.err.println("Unsupported statement type: " + node.getType());
                return "";
        }
    }

    private static String NORMALCFGStmtNodeToStr(CFGStmtNode node){
        return applyLabel(node, node.getContent());
    }

    private static String IF_ELSECFGStmtNodeToStr(CFGStmtNode node){
        return applyLabel(node, node.getContent());
    }

    private static String CALLCFGStmtNodeToStr(CFGStmtNode node){
        return applyLabel(node, node.getContent());
    }   

    private static String LETCFGStmtNodeToStr(CFGStmtNode node){
        return applyLabel(node, node.getContent());
    }

    private static String ROOTCFGStmtNodeToStr(CFGStmtNode node){
        return "";
    }

    private static String SKIPCFGStmtNodeToStr(CFGStmtNode node){
        return "";
    }
    
    private static String UNCHANGEDCFGStmtNodeToStr(CFGStmtNode node){
        return applyLabel(node, node.getContent());
    }
    
    private static String CASECFGStmtNodeToStr(CFGStmtNode node){
        return applyLabel(node, node.getContent());
    }
    
    private static String CHOOSECFGStmtNodeToStr(CFGStmtNode node){
        return applyLabel(node, node.getContent());
    }
    
    private static String EXISTSCFGStmtNodeToStr(CFGStmtNode node){
        return applyLabel(node, node.getContent());
    }
    
    private static String FORALLCFGStmtNodeToStr(CFGStmtNode node){
        return applyLabel(node, node.getContent());
    }
    
    private static String CASE_ARMCFGStmtNodeToStr(CFGStmtNode node){
        return applyLabel(node, node.getContent());
    }
    
    private static String DISJUNCTIONCFGStmtNodeToStr(CFGStmtNode node){
        return ""; // DISJUNCTION nodes don't have content, only branches
    }

    private static String applyLabel(CFGStmtNode node, String baseContent) {
        String content = baseContent == null ? "" : baseContent.trim();
        String label = node.getLabel();
        if (label == null || label.isEmpty()) {
            return content;
        }

        String prefix = label + " ==";
        if (content.startsWith(prefix)) {
            return content;
        }

        if (content.isEmpty()) {
            return prefix;
        }

        return prefix + " " + content;
    }
}
