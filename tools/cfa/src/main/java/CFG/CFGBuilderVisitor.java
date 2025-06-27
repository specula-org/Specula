package CFG;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.Queue;
import java.util.LinkedList;

import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.LexerAction;
import org.antlr.v4.runtime.tree.*;

import parser.TLAPlusParser;
import parser.TLAPlusParserBaseVisitor;

// Visitor class for traversing ParseTree and building CFG
public class CFGBuilderVisitor extends TLAPlusParserBaseVisitor<Object> {
    private static final String IGNORE_OPERATORS = "^(Init|Next|Spec|vars)";
    private List<String> constants = new ArrayList<>();
    private List<String> variables = new ArrayList<>();
    private List<CFGFuncNode> cfgFuncNodes = new ArrayList<>();
    private int indentationLevel = 0; 

    public List<String> getVariables() {
        return variables;
    }

    public List<String> getConstants() {
        return constants;
    }

    public List<CFGFuncNode> getCfgFuncNodes() {
        return cfgFuncNodes;
    }

    @Override
    public Void visitModule(TLAPlusParser.ModuleContext ctx) {
        // System.out.println("Visiting module: " + getFullText(ctx));
        for (TLAPlusParser.UnitContext unitCtx : ctx.unit()) {
            visitUnit(unitCtx);
        }
        return null;
    }

    @Override 
    public Void visitUnit(TLAPlusParser.UnitContext ctx) {
        if (ctx.variableDeclaration() != null) {
            visitVariableDeclaration(ctx.variableDeclaration());
        } else if (ctx.constantDeclaration() != null) {
            visitConstantDeclaration(ctx.constantDeclaration());
        } else if (ctx.operatorDefinition() != null) {
            visitOperatorDefinition(ctx.operatorDefinition());
        } else if (ctx.functionDefinition() != null) {
            visitFunctionDefinition(ctx.functionDefinition());
        } else if (ctx.instance() != null) {
            visitInstance(ctx.instance());
        } else if (ctx.moduleDefinition() != null) {
            visitModuleDefinition(ctx.moduleDefinition());
        } else if (ctx.assumption() != null) {
            visitAssumption(ctx.assumption());
        } else if (ctx.theorem() != null) {
            visitTheorem(ctx.theorem());
        } else if (ctx.module() != null) {
            visitModule(ctx.module());
        }
        return null;
    }

    @Override
    public Void visitConstantDeclaration(TLAPlusParser.ConstantDeclarationContext ctx) {
        // Get all constant identifiers and add them to constants list
        if (ctx.opDecl() != null) {
            for (var id : ctx.opDecl()) {
                constants.add(id.getText());
                // System.out.println("Constant: " + id.getText());
            }
        }
        return null;
    }
    @Override
    public Void visitVariableDeclaration(TLAPlusParser.VariableDeclarationContext ctx) {
        // Get all variable identifiers and add them to variables list
        if (ctx.Identifier() != null) {
            for (var id : ctx.Identifier()) {
                variables.add(id.getText());
                // System.out.println("Variable: " + id.getText());
            }
        }
        return null;
    }

    @Override
    public Void visitOperatorDefinition(TLAPlusParser.OperatorDefinitionContext ctx) {
        String text = getFullText(ctx);
        Pattern pattern = Pattern.compile(IGNORE_OPERATORS);
        Matcher matcher = pattern.matcher(text);

        if (matcher.find()) {
            // If string starts with specified keywords, ignore it
            return null;
        }

        // System.out.println("Visiting operator definition: " + text);
        // Handle nonFixLHS EQUALS body case
        if (ctx.nonFixLHS() != null) {
            // Visit nonFixLHS to get function name and parameter list
            List<String> funcInfo = visitNonFixLHS(ctx.nonFixLHS());
            String funcName = funcInfo.get(0);
            List<String> parameters = new ArrayList<>();
            if (funcInfo.size() > 1) {
                parameters = funcInfo.subList(1, funcInfo.size());
            }
            
            // Initialize function node
            CFGFuncNode funcNode = new CFGFuncNode(funcName, parameters);
            
            CFGStmtNode root = new CFGStmtNode(indentationLevel, "root", null, CFGStmtNode.StmtType.ROOT);

            // Visit function body to get statement nodes and edge information
            CFGStmtNode bodyInfo = visitBody(ctx.body());

            root.addChild(bodyInfo);
            funcNode.setRoot(root);
            
            // Add function node to CFG

            cfgFuncNodes.add(funcNode);
        }
        else {
            // Handle special cases
            System.out.println("Special case: " + getFullText(ctx));
        }
        return null;
    }

    @Override
    public List<String> visitNonFixLHS(TLAPlusParser.NonFixLHSContext ctx) {
        // System.out.println("visitNonFixLHS: " + getFullText(ctx));
        List<String> funcInfo = new ArrayList<>();
        
        // Get function name (first identifier)
        if (ctx.Identifier().size() > 0) {
            funcInfo.add(ctx.Identifier(0).getText());
            
            // If there is a parameter list
            if (ctx.LPAREN() != null) {
                // Starting from the second identifier, all are parameters
                for (int i = 1; i < ctx.Identifier().size(); i++) {
                    funcInfo.add(ctx.Identifier(i).getText());
                }
            }
        }
        // System.out.println("funcInfo: " + funcInfo);
        return funcInfo;
    }

        
    @Override
    public CFGStmtNode visitBody(TLAPlusParser.BodyContext ctx) {
        indentationLevel++;
        // System.out.println("Visit body: " + ctx.getStart().getInputStream()
        // .getText(Interval.of(ctx.getStart().getStartIndex(), 
        //                     ctx.getStop().getStopIndex())));
        // If there is only one expression, return the visit result directly
        // if (ctx.statement().size() == 1) {
        //     CFGStmtNode return_val = (CFGStmtNode) visit(ctx.statement(0));
        //     indentationLevel--;
        //     return return_val;
        // }
        
        // When there are multiple expressions, connect them in order
        // CFGStmtNode firstStmt = null;
        // List<CFGStmtNode> prevLeaves = new ArrayList<>();
        
        // // Traverse all expressions
        // for (TLAPlusParser.StatementContext stmt : ctx.statement()) {
        //     CFGStmtNode currStmt = (CFGStmtNode) visit(stmt);
        //     // Record the first statement as return value
        //     if (firstStmt == null) {
        //         firstStmt = currStmt;
        //     } else {
        //         // Point all leaf nodes of previous statement to root node of current statement
        //         for (CFGStmtNode leaf : prevLeaves) {
        //             leaf.addChild(currStmt);
        //         }
        //     }
            
        //     // Update leaf node list of previous statement
        //     prevLeaves.clear();
        //     findLeafNodes(currStmt, prevLeaves);
        // }

        CFGStmtNode firstStmt = visitAobody(ctx.aobody());
        indentationLevel--;
        return firstStmt;
    }
    
    @Override
    public CFGStmtNode visitIfExpression(TLAPlusParser.IfExpressionContext ctx) {
        CFGStmtNode ifStmt = new CFGStmtNode(indentationLevel, "IF " + getFullText(ctx.expression()) + " THEN", ctx, CFGStmtNode.StmtType.IF_ELSE);
        // Distinguish then and else expressions
        CFGStmtNode thenNode = null;
        thenNode = visitThenExpression(ctx.thenExpression());
        // Visit else branch
        CFGStmtNode elseNode = null;
        elseNode = visitElseExpression(ctx.elseExpression());
        
        // Connect if node with then/else branches
        ifStmt.addChild(thenNode);
        ifStmt.addChild(elseNode);
        indentationLevel--;
        return ifStmt;
    }

    @Override
    public CFGStmtNode visitThenExpression(TLAPlusParser.ThenExpressionContext ctx) {
        CFGStmtNode skipNode = new CFGStmtNode(indentationLevel, "skip", null, CFGStmtNode.StmtType.SKIP);
        CFGStmtNode thenNode = null;
        List<CFGStmtNode> thenLeaves = new ArrayList<>();
        indentationLevel++;
        for (TLAPlusParser.AobodyContext aobody : ctx.aobody()) {
            CFGStmtNode currStmt = visitAobody(aobody);
            
            if (thenNode == null) {
                thenNode = currStmt;
            } else {
                // Point all leaf nodes of previous statement to current statement
                for (CFGStmtNode leaf : thenLeaves) {
                    leaf.addChild(currStmt); 
                }
            }
            
            // Update leaf node list
            thenLeaves.clear();
            findLeafNodes(currStmt, thenLeaves);
        }
        skipNode.addChild(thenNode);
        return skipNode;
    }

    @Override
    public CFGStmtNode visitElseExpression(TLAPlusParser.ElseExpressionContext ctx) {
        CFGStmtNode elseNode = visitAobody(ctx.aobody());
        CFGStmtNode ELSEnode = new CFGStmtNode(indentationLevel, "ELSE", null, CFGStmtNode.StmtType.NORMAL);
        ELSEnode.addChild(elseNode);
        
        return ELSEnode;
    }

    public CFGStmtNode visitAobody(TLAPlusParser.AobodyContext ctx) {
        if (ctx instanceof TLAPlusParser.NonindentedSlashBackslashContext) {
            return visitNonindentedSlashBackslash((TLAPlusParser.NonindentedSlashBackslashContext) ctx);
        } else if (ctx instanceof TLAPlusParser.NonindentedBackslashSlashContext) {
            return visitNonindentedBackslashSlash((TLAPlusParser.NonindentedBackslashSlashContext) ctx);
        } else if (ctx instanceof TLAPlusParser.IndentedSlashBackslashContext) {
            return visitIndentedSlashBackslash((TLAPlusParser.IndentedSlashBackslashContext) ctx);
        } else if (ctx instanceof TLAPlusParser.IndentedBackslashSlashContext) {
            return visitIndentedBackslashSlash((TLAPlusParser.IndentedBackslashSlashContext) ctx);
        } else if (ctx instanceof TLAPlusParser.AobodyStatementContext) {
            return visitAobodyStatement((TLAPlusParser.AobodyStatementContext) ctx);
        } else {
            System.err.println("Unknown aobody context type: " + ctx.getClass().getName());
            return null;
        }
    }

    @Override
    public CFGStmtNode visitNonindentedSlashBackslash (TLAPlusParser.NonindentedSlashBackslashContext ctx) {
        List<TLAPlusParser.AobodyContext> indentedBodies = ctx.aobody().stream().collect(Collectors.toList());
        // Handle first aobody specially
        CFGStmtNode firstBody = visitAobody(indentedBodies.get(0));
        AddStrToContentHead(firstBody, "/\\ ");
        // Start connecting
        List<CFGStmtNode> prevLeaves = new ArrayList<>();
        findLeafNodes(firstBody, prevLeaves);
        for (int i = 1; i < indentedBodies.size(); i++) {
            CFGStmtNode body = visitAobody(indentedBodies.get(i));
            AddStrToContentHead(body, "/\\ ");
            for (CFGStmtNode leaf: prevLeaves){
                leaf.addChild(body);
            }
            prevLeaves.clear();
            findLeafNodes(body, prevLeaves);
        }
        return firstBody;
    }

    @Override
    public CFGStmtNode visitNonindentedBackslashSlash (TLAPlusParser.NonindentedBackslashSlashContext ctx) {
        // Handle \/ connected expressions
        List<TLAPlusParser.AobodyContext> indentedBodies = ctx.aobody().stream().collect(Collectors.toList());
        // Handle first aobody specially
        CFGStmtNode firstBody = visitAobody(indentedBodies.get(0));
        AddStrToContentHead(firstBody, "\\/");
        CFGStmtNode skipNode = new CFGStmtNode(indentationLevel, "skip", null, CFGStmtNode.StmtType.SKIP);
        skipNode.addChild(firstBody);
        for (int i = 1; i < indentedBodies.size(); i++) {
            CFGStmtNode body = visitAobody(indentedBodies.get(i));
            AddStrToContentHead(body, "\\/");
            skipNode.addChild(body);
        }
        return skipNode;
    }

    @Override
    public CFGStmtNode visitIndentedSlashBackslash (TLAPlusParser.IndentedSlashBackslashContext ctx) {
        List<TLAPlusParser.AobodyContext> indentedBodies = ctx.aobody().stream().collect(Collectors.toList());
        // Handle first aobody specially
        CFGStmtNode firstBody = visitAobody(indentedBodies.get(0));
        indentationLevel++;
        AddStrToContentHead(firstBody, "/\\ ");
        // Start connecting
        List<CFGStmtNode> prevLeaves = new ArrayList<>();
        findLeafNodes(firstBody, prevLeaves);
        for (int i = 1; i < indentedBodies.size(); i++) {
            CFGStmtNode body = visitAobody(indentedBodies.get(i));
            AddStrToContentHead(body, "/\\ ");
            for (CFGStmtNode leaf: prevLeaves){
                leaf.addChild(body);
            }
            prevLeaves.clear();
            findLeafNodes(body, prevLeaves);
        }
        indentationLevel--;
        return firstBody;
    }

    @Override
    public CFGStmtNode visitIndentedBackslashSlash (TLAPlusParser.IndentedBackslashSlashContext ctx) {
        // Handle \/ connected expressions
        List<TLAPlusParser.AobodyContext> indentedBodies = ctx.aobody().stream().collect(Collectors.toList());
        // Handle first aobody specially
        CFGStmtNode firstBody = visitAobody(indentedBodies.get(0));
        indentationLevel++;
        AddStrToContentHead(firstBody, "\\/");
        CFGStmtNode skipNode = new CFGStmtNode(indentationLevel, "skip", null, CFGStmtNode.StmtType.SKIP);
        skipNode.addChild(firstBody);
        for (int i = 1; i < indentedBodies.size(); i++) {
            CFGStmtNode body = visitAobody(indentedBodies.get(i));
            AddStrToContentHead(body, "\\/");
            skipNode.addChild(body);
        }
        indentationLevel--;
        return skipNode;
    }

    @Override
    public CFGStmtNode visitAobodyStatement (TLAPlusParser.AobodyStatementContext ctx) {
        return visitStatement(ctx.statement());
    }

    @Override
    public CFGStmtNode visitStatement(TLAPlusParser.StatementContext ctx) {
        // System.out.println("Visit statement: " + ctx.getStart().getInputStream(
        // .getText(Interval.of(ctx.getStart().getStartIndex(), 
        //                     ctx.getStop().getStopIndex())));
        // If there is only one expression, return the visit result directly
        if (ctx.expression().size() == 1) {
            return (CFGStmtNode) visit(ctx.expression(0));
        }
        
        // When there are multiple expressions, connect them in order
        CFGStmtNode firstStmt = null;
        List<CFGStmtNode> prevLeaves = new ArrayList<>();
        
        // Traverse all expressions
        for (TLAPlusParser.ExpressionContext expr : ctx.expression()) {
            CFGStmtNode currStmt = (CFGStmtNode) visit(expr);
            // Record the first statement as return value
            if (firstStmt == null) {
                firstStmt = currStmt;
            } else {
                // Point all leaf nodes of previous statement to root node of current statement
                for (CFGStmtNode leaf : prevLeaves) {
                    leaf.addChild(currStmt);
                }
            }
            
            // Update leaf node list of previous statement
            prevLeaves.clear();
            findLeafNodes(currStmt, prevLeaves);
        }
        return firstStmt;
    }

    @Override
    public CFGStmtNode visitFunctionCall(TLAPlusParser.FunctionCallContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override 
    public CFGStmtNode visitPrefixOperation(TLAPlusParser.PrefixOperationContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitIdentifierExpression(TLAPlusParser.IdentifierExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitParenthesizedExpression(TLAPlusParser.ParenthesizedExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitQuantifierExpression(TLAPlusParser.QuantifierExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitSimpleQuantifierExpression(TLAPlusParser.SimpleQuantifierExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitChooseExpression(TLAPlusParser.ChooseExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitChooseInExpression(TLAPlusParser.ChooseInExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitEmptySet(TLAPlusParser.EmptySetContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitSetExpression(TLAPlusParser.SetExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitSetComprehension(TLAPlusParser.SetComprehensionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitSetQuantifier(TLAPlusParser.SetQuantifierContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitMappingExpression(TLAPlusParser.MappingExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitArrowExpression(TLAPlusParser.ArrowExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitMapstoExpression(TLAPlusParser.MapstoExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitColonExpression(TLAPlusParser.ColonExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitExceptExpression(TLAPlusParser.ExceptExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitDoubleLessExpression(TLAPlusParser.DoubleLessExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitBracketUnderscoreExpression(TLAPlusParser.BracketUnderscoreExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitDoubleLessUnderscoreExpression(TLAPlusParser.DoubleLessUnderscoreExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitFairnessExpression(TLAPlusParser.FairnessExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitCaseExpression(TLAPlusParser.CaseExpressionContext ctx) {
        CFGStmtNode skipNode = new CFGStmtNode(indentationLevel, "skip", null, CFGStmtNode.StmtType.SKIP);
        
        // Handle first branch
        CFGStmtNode firstCaseNode = new CFGStmtNode(indentationLevel, "CASE " + getFullText(ctx.expression(0)) + " ->", ctx, CFGStmtNode.StmtType.NORMAL);
        skipNode.addChild(firstCaseNode);
        indentationLevel++;
        CFGStmtNode firstBody = visitBody(ctx.body(0));
        firstCaseNode.addChild(firstBody);
        
        // Handle intermediate branches
        for (int i = 1; i < ctx.expression().size(); i++) {
            CFGStmtNode caseNode = new CFGStmtNode(indentationLevel, "[] " + getFullText(ctx.expression(i)) + " ->", ctx, CFGStmtNode.StmtType.NORMAL);
            skipNode.addChild(caseNode);
            CFGStmtNode body = visitBody(ctx.body(i));
            caseNode.addChild(body);
        }
        
        // Handle last OTHER branch (if any)
        if (ctx.OTHER() != null) {
            CFGStmtNode otherNode = new CFGStmtNode(indentationLevel, "[] OTHER ->", ctx, CFGStmtNode.StmtType.NORMAL);
            skipNode.addChild(otherNode);
            CFGStmtNode otherBody = visitBody(ctx.body(ctx.body().size() - 1));
            otherNode.addChild(otherBody);
        }
        indentationLevel--;
        return skipNode;
    }

    @Override
    public CFGStmtNode visitLetExpression(TLAPlusParser.LetExpressionContext ctx) {

        StringBuilder content = new StringBuilder();
        List<String> tempVars = new ArrayList<>();
        // Get
        int i = 0;
        while (i < ctx.children.size()) {
            if (ctx.children.get(i).getText().equals("LET")) {
                i++;
                // Collect all definitions before BIGIN
                // If it is not operatorDefinition | functionDefinition | moduleDefinition, continue
                if (!(ctx.children.get(i) instanceof TLAPlusParser.OperatorDefinitionContext ||
                      ctx.children.get(i) instanceof TLAPlusParser.FunctionDefinitionContext ||
                      ctx.children.get(i) instanceof TLAPlusParser.ModuleDefinitionContext)) {
                    i++;
                    continue;
                }
                // Add temporary variables
                if (ctx.children.get(i) instanceof TLAPlusParser.ModuleDefinitionContext) {
                    TLAPlusParser.ModuleDefinitionContext moduleCtx = (TLAPlusParser.ModuleDefinitionContext) ctx.children.get(i);
                    if (moduleCtx.nonFixLHS() != null) {
                        for (TerminalNode identifier : moduleCtx.nonFixLHS().Identifier()) {
                            tempVars.add(identifier.getText());
                        }
                    }
                } else if (ctx.children.get(i) instanceof TLAPlusParser.FunctionDefinitionContext) {
                    TLAPlusParser.FunctionDefinitionContext funcCtx = (TLAPlusParser.FunctionDefinitionContext) ctx.children.get(i);
                    tempVars.add(funcCtx.Identifier().getText());
                } else if (ctx.children.get(i) instanceof TLAPlusParser.OperatorDefinitionContext) {
                    TLAPlusParser.OperatorDefinitionContext opCtx = (TLAPlusParser.OperatorDefinitionContext) ctx.children.get(i);
                    if (opCtx.nonFixLHS() != null) {
                        for (TerminalNode identifier : opCtx.nonFixLHS().Identifier()) {
                            tempVars.add(identifier.getText());
                        }
                    } else if (opCtx.Identifier() != null) {
                        for (TerminalNode identifier : opCtx.Identifier()) {
                            tempVars.add(identifier.getText());
                        }
                    }
                }

                while (i < ctx.children.size() && !ctx.children.get(i).getText().equals("IN")) {
                    if(i == 1){
                        if (ctx.children.get(i) instanceof ParserRuleContext) {
                            content.append(getFullText((ParserRuleContext) ctx.children.get(i))).append("\n");
                        } else {
                            // Handle terminal nodes, directly get their text
                            // System.err.println("Terminal node: " + ctx.children.get(i).getText());
                            content.append(ctx.children.get(i).getText()).append("\n");
                            // Or handle terminal nodes using other methods if needed
                        }
                    } else{
                        if (ctx.children.get(i) instanceof ParserRuleContext) {
                            content.append(" ".repeat((indentationLevel + 1) * 4) + getFullText((ParserRuleContext) ctx.children.get(i))).append("\n");
                        } else {
                            // System.err.println("Terminal node: " + ctx.children.get(i).getText());
                            content.append(" ".repeat((indentationLevel + 1) * 4) + ctx.children.get(i).getText()).append("\n");
                        }
                    }
                    i++;
                }
                break;
            }
            i++;
        }
        // Remove empty lines from content
        content = new StringBuilder(content.toString().replaceAll("(?m)^[ \t]*\r?\n", ""));
        String cleanedContent = content.toString().replaceAll("([\\n\\r]+\\s*)+$", "");
        CFGStmtNode letNode = new CFGStmtNode(indentationLevel, "LET " + cleanedContent + " IN", ctx, CFGStmtNode.StmtType.LET);
        letNode.setTemporaryVariables(tempVars);
        // System.out.println("tempVars: " + tempVars);
        if (tempVars.isEmpty()){
            // Error
            System.err.println("No variables are defined in the LET expression");
            System.exit(1);
        }
        CFGStmtNode body = visitBody(ctx.body());
        letNode.addChild(body);
        return letNode;
    }

    @Override
    public CFGStmtNode visitSlashBackslashExpression(TLAPlusParser.SlashBackslashExpressionContext ctx) {
        if (ctx.aobody() != null) {
            CFGStmtNode body = visitAobody(ctx.aobody());
            AddStrToContentHead(body, "/\\ ");
            return body;
        }
        return null;
    }                                                                  

    @Override
    public CFGStmtNode visitBackslashSlashExpression(TLAPlusParser.BackslashSlashExpressionContext ctx) {
        if (ctx.aobody() != null) {
            CFGStmtNode body = visitAobody(ctx.aobody());
            AddStrToContentHead(body, "\\/");
            return body;
        }
        return null;    }

    @Override
    public CFGStmtNode visitNumberExpression(TLAPlusParser.NumberExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitStringExpression(TLAPlusParser.StringExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override
    public CFGStmtNode visitAtExpression(TLAPlusParser.AtExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    @Override 
    public Void visitFunctionDefinition(TLAPlusParser.FunctionDefinitionContext ctx) {
        // System.out.println("Visit function definition: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitInstance(TLAPlusParser.InstanceContext ctx) {
        // System.out.println("Visit instance: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitModuleDefinition(TLAPlusParser.ModuleDefinitionContext ctx) {
        // System.out.println("Visit module definition: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitAssumption(TLAPlusParser.AssumptionContext ctx) {
        // System.out.println("Visit assumption: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitTheorem(TLAPlusParser.TheoremContext ctx) {
        // System.out.println("Visit theorem: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitOpDecl(TLAPlusParser.OpDeclContext ctx) {
        // System.out.println("Visit operator declaration: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitQuantifierBound(TLAPlusParser.QuantifierBoundContext ctx) {
        // System.out.println("Visit quantifier bound: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitSubstitution(TLAPlusParser.SubstitutionContext ctx) {
        // System.out.println("Visit substitution: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitArgument(TLAPlusParser.ArgumentContext ctx) {
        // System.out.println("Visit argument: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitInstancePrefix(TLAPlusParser.InstancePrefixContext ctx) {
        // System.out.println("Visit instance prefix: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitGeneralIdentifier(TLAPlusParser.GeneralIdentifierContext ctx) {
        // System.out.println("Visit general identifier: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitGeneralPrefixOp(TLAPlusParser.GeneralPrefixOpContext ctx) {
        // System.out.println("Visit general prefix operator: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitGeneralInfixOp(TLAPlusParser.GeneralInfixOpContext ctx) {
        // System.out.println("Visit general infix operator: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitGeneralPostfixOp(TLAPlusParser.GeneralPostfixOpContext ctx) {
        // System.out.println("Visit general postfix operator: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitRightExpression(TLAPlusParser.RightExpressionContext ctx) {
        // System.out.println("Visit right expression: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitIdentifierOrTuple(TLAPlusParser.IdentifierOrTupleContext ctx) {
        // System.out.println("Visit identifier or tuple: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitReservedWord(TLAPlusParser.ReservedWordContext ctx) {
        // System.out.println("Visit reserved word: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitPrefixOp(TLAPlusParser.PrefixOpContext ctx) {
        // System.out.println("Visit prefix operator: " + getFullText(ctx));
        return null;
    }


    @Override
    public Void visitPostfixOp(TLAPlusParser.PostfixOpContext ctx) {
        // System.out.println("Visit postfix operator: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitInfixOp(TLAPlusParser.InfixOpContext ctx) {
        // System.out.println("Visit infix operator: " + getFullText(ctx));
        return null;
    }

    // Helper method: find all leaf nodes of a node
    private void findLeafNodes(CFGStmtNode node, List<CFGStmtNode> leaves) {
        if (node == null) return; 

        if ((node.getChildren() == null || node.getChildren().isEmpty()) && (!leaves.contains(node))) {
            leaves.add(node);
            return;
        }
        
        for (CFGStmtNode child : node.getChildren()) {
            findLeafNodes(child, leaves);
        }
    }
    
    private void AddStrToContentHead(CFGStmtNode node, String str){
        List<CFGStmtNode> queue = new ArrayList<CFGStmtNode>();
        queue.add(node);
        while (!queue.isEmpty()) {
            CFGStmtNode currNode = queue.remove(0);
            if (currNode.getChildren() != null) {
                queue.addAll(currNode.getChildren());
            }
            if (currNode.getType() != CFGStmtNode.StmtType.SKIP && currNode.getType() != CFGStmtNode.StmtType.ROOT) {
                currNode.setContent(str + currNode.getContent());
                break; 
            }
        }
    }
    private String getFullText(ParserRuleContext ctx) {
        if (ctx.getStart() == null || ctx.getStop() == null) {
            return ""; // Handle empty context
        }
        return ctx.getStart().getInputStream()
            .getText(Interval.of(ctx.getStart().getStartIndex(), 
                                ctx.getStop().getStopIndex()));
    }
}


