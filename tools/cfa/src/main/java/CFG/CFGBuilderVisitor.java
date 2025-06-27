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
        // 获取所有常量标识符并添加到 constants 列表中
        if (ctx.opDecl() != null) {
            for (var id : ctx.opDecl()) {
                constants.add(id.getText());
                // System.out.println("常量: " + id.getText());
            }
        }
        return null;
    }
    @Override
    public Void visitVariableDeclaration(TLAPlusParser.VariableDeclarationContext ctx) {
        // 获取所有变量标识符并添加到 variables 列表中
        if (ctx.Identifier() != null) {
            for (var id : ctx.Identifier()) {
                variables.add(id.getText());
                // System.out.println("变量: " + id.getText());
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
            // 如果字符串以指定关键字开头，则忽略
            return null;
        }

        // System.out.println("访问操作符定义: " + text);
        // 处理 nonFixLHS EQUALS body 的情况
        if (ctx.nonFixLHS() != null) {
            // 访问 nonFixLHS 获取函数名和参数列表
            List<String> funcInfo = visitNonFixLHS(ctx.nonFixLHS());
            String funcName = funcInfo.get(0);
            List<String> parameters = new ArrayList<>();
            if (funcInfo.size() > 1) {
                parameters = funcInfo.subList(1, funcInfo.size());
            }
            
            // 初始化函数节点
            CFGFuncNode funcNode = new CFGFuncNode(funcName, parameters);
            
            CFGStmtNode root = new CFGStmtNode(indentationLevel, "root", null, CFGStmtNode.StmtType.ROOT);

            // 访问函数体,获取语句节点和边的信息
            CFGStmtNode bodyInfo = visitBody(ctx.body());

            root.addChild(bodyInfo);
            funcNode.setRoot(root);
            
            // 将函数节点添加到CFG中

            cfgFuncNodes.add(funcNode);
        }
        else {
            // 处理特殊情况
            System.out.println("Special case: " + getFullText(ctx));
        }
        return null;
    }

    @Override
    public List<String> visitNonFixLHS(TLAPlusParser.NonFixLHSContext ctx) {
        // System.out.println("visitNonFixLHS: " + getFullText(ctx));
        List<String> funcInfo = new ArrayList<>();
        
        // 获取函数名(第一个标识符)
        if (ctx.Identifier().size() > 0) {
            funcInfo.add(ctx.Identifier(0).getText());
            
            // 如果有参数列表
            if (ctx.LPAREN() != null) {
                // 从第二个标识符开始都是参数
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
        // System.out.println("访问Body: " + ctx.getStart().getInputStream()
        // .getText(Interval.of(ctx.getStart().getStartIndex(), 
        //                     ctx.getStop().getStopIndex())));
        // 如果只有一个表达式,直接返回访问结果
        // if (ctx.statement().size() == 1) {
        //     CFGStmtNode return_val = (CFGStmtNode) visit(ctx.statement(0));
        //     indentationLevel--;
        //     return return_val;
        // }
        
        // 有多个表达式时,按顺序连接
        // CFGStmtNode firstStmt = null;
        // List<CFGStmtNode> prevLeaves = new ArrayList<>();
        
        // // 遍历所有表达式
        // for (TLAPlusParser.StatementContext stmt : ctx.statement()) {
        //     CFGStmtNode currStmt = (CFGStmtNode) visit(stmt);
        //     // 记录第一个语句作为返回值
        //     if (firstStmt == null) {
        //         firstStmt = currStmt;
        //     } else {
        //         // 将前一个语句的所有叶子节点指向当前语句的根节点
        //         for (CFGStmtNode leaf : prevLeaves) {
        //             leaf.addChild(currStmt);
        //         }
        //     }
            
        //     // 更新前一个语句的叶子节点列表
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
        // 区分 then 和 else 的 expression
        CFGStmtNode thenNode = null;
        thenNode = visitThenExpression(ctx.thenExpression());
        // 访问 else 分支
        CFGStmtNode elseNode = null;
        elseNode = visitElseExpression(ctx.elseExpression());
        
        // 将 if 节点与 then/else 分支连接
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
                // 将前一个语句的所有叶子节点指向当前语句
                for (CFGStmtNode leaf : thenLeaves) {
                    leaf.addChild(currStmt); 
                }
            }
            
            // 更新叶子节点列表
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
        // 第一个 aobody 特殊处理
        CFGStmtNode firstBody = visitAobody(indentedBodies.get(0));
        AddStrToContentHead(firstBody, "/\\ ");
        // 开始连接
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
        // 处理\/连接的表达式
        List<TLAPlusParser.AobodyContext> indentedBodies = ctx.aobody().stream().collect(Collectors.toList());
        // 第一个 aobody 特殊处理
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
        // 第一个 aobody 特殊处理
        CFGStmtNode firstBody = visitAobody(indentedBodies.get(0));
        indentationLevel++;
        AddStrToContentHead(firstBody, "/\\ ");
        // 开始连接
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
        // 处理\/连接的表达式
        List<TLAPlusParser.AobodyContext> indentedBodies = ctx.aobody().stream().collect(Collectors.toList());
        // 第一个 aobody 特殊处理
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
        // System.out.println("访问Stmt: " + ctx.getStart().getInputStream()
        // .getText(Interval.of(ctx.getStart().getStartIndex(), 
        //                     ctx.getStop().getStopIndex())));
        // 如果只有一个表达式,直接返回访问结果
        if (ctx.expression().size() == 1) {
            return (CFGStmtNode) visit(ctx.expression(0));
        }
        
        // 有多个表达式时,按顺序连接
        CFGStmtNode firstStmt = null;
        List<CFGStmtNode> prevLeaves = new ArrayList<>();
        
        // 遍历所有表达式
        for (TLAPlusParser.ExpressionContext expr : ctx.expression()) {
            CFGStmtNode currStmt = (CFGStmtNode) visit(expr);
            // 记录第一个语句作为返回值
            if (firstStmt == null) {
                firstStmt = currStmt;
            } else {
                // 将前一个语句的所有叶子节点指向当前语句的根节点
                for (CFGStmtNode leaf : prevLeaves) {
                    leaf.addChild(currStmt);
                }
            }
            
            // 更新前一个语句的叶子节点列表
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
        
        // 处理第一个分支
        CFGStmtNode firstCaseNode = new CFGStmtNode(indentationLevel, "CASE " + getFullText(ctx.expression(0)) + " ->", ctx, CFGStmtNode.StmtType.NORMAL);
        skipNode.addChild(firstCaseNode);
        indentationLevel++;
        CFGStmtNode firstBody = visitBody(ctx.body(0));
        firstCaseNode.addChild(firstBody);
        
        // 处理中间的分支
        for (int i = 1; i < ctx.expression().size(); i++) {
            CFGStmtNode caseNode = new CFGStmtNode(indentationLevel, "[] " + getFullText(ctx.expression(i)) + " ->", ctx, CFGStmtNode.StmtType.NORMAL);
            skipNode.addChild(caseNode);
            CFGStmtNode body = visitBody(ctx.body(i));
            caseNode.addChild(body);
        }
        
        // 处理最后的 OTHER 分支（如果有）
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
        // 获取 LET 和 BIGIN 之间的所有定义
        int i = 0;
        while (i < ctx.children.size()) {
            if (ctx.children.get(i).getText().equals("LET")) {
                i++;
                // 收集直到遇到 BIGIN 之前的所有定义
                // 如果不是 operatorDefinition | functionDefinition | moduleDefinition，则 continue 
                if (!(ctx.children.get(i) instanceof TLAPlusParser.OperatorDefinitionContext ||
                      ctx.children.get(i) instanceof TLAPlusParser.FunctionDefinitionContext ||
                      ctx.children.get(i) instanceof TLAPlusParser.ModuleDefinitionContext)) {
                    i++;
                    continue;
                }
                // 添加临时变量
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
                            // 处理终端节点，直接获取其文本
                            // System.err.println("终端节点: " + ctx.children.get(i).getText());
                            content.append(ctx.children.get(i).getText()).append("\n");
                            // 或者根据需要使用其他方法处理终端节点
                        }
                    } else{
                        if (ctx.children.get(i) instanceof ParserRuleContext) {
                            content.append(" ".repeat((indentationLevel + 1) * 4) + getFullText((ParserRuleContext) ctx.children.get(i))).append("\n");
                        } else {
                            // System.err.println("终端节点: " + ctx.children.get(i).getText());
                            content.append(" ".repeat((indentationLevel + 1) * 4) + ctx.children.get(i).getText()).append("\n");
                        }
                    }
                    i++;
                }
                break;
            }
            i++;
        }
        // 去掉 content 里的空行
        content = new StringBuilder(content.toString().replaceAll("(?m)^[ \t]*\r?\n", ""));
        String cleanedContent = content.toString().replaceAll("([\\n\\r]+\\s*)+$", "");
        CFGStmtNode letNode = new CFGStmtNode(indentationLevel, "LET " + cleanedContent + " IN", ctx, CFGStmtNode.StmtType.LET);
        letNode.setTemporaryVariables(tempVars);
        // System.out.println("tempVars: " + tempVars);
        if (tempVars.isEmpty()){
            // 报错
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
        // System.out.println("访问函数定义: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitInstance(TLAPlusParser.InstanceContext ctx) {
        // System.out.println("访问实例: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitModuleDefinition(TLAPlusParser.ModuleDefinitionContext ctx) {
        // System.out.println("访问模块定义: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitAssumption(TLAPlusParser.AssumptionContext ctx) {
        // System.out.println("访问假设: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitTheorem(TLAPlusParser.TheoremContext ctx) {
        // System.out.println("访问定理: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitOpDecl(TLAPlusParser.OpDeclContext ctx) {
        // System.out.println("访问操作符声明: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitQuantifierBound(TLAPlusParser.QuantifierBoundContext ctx) {
        // System.out.println("访问量词绑定: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitSubstitution(TLAPlusParser.SubstitutionContext ctx) {
        // System.out.println("访问替换: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitArgument(TLAPlusParser.ArgumentContext ctx) {
        // System.out.println("访问参数: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitInstancePrefix(TLAPlusParser.InstancePrefixContext ctx) {
        // System.out.println("
        return null;
    }

    @Override
    public Void visitGeneralIdentifier(TLAPlusParser.GeneralIdentifierContext ctx) {
        // System.out.println("访问通用标识符: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitGeneralPrefixOp(TLAPlusParser.GeneralPrefixOpContext ctx) {
        // System.out.println("访问通用前缀操作符: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitGeneralInfixOp(TLAPlusParser.GeneralInfixOpContext ctx) {
        // System.out.println("访问通用中缀操作符: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitGeneralPostfixOp(TLAPlusParser.GeneralPostfixOpContext ctx) {
        // System.out.println("访问通用后缀操作符: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitRightExpression(TLAPlusParser.RightExpressionContext ctx) {
        // System.out.println("访问右表达式: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitIdentifierOrTuple(TLAPlusParser.IdentifierOrTupleContext ctx) {
        // System.out.println("访问标识符或元组: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitReservedWord(TLAPlusParser.ReservedWordContext ctx) {
        // System.out.println("访问保留字: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitPrefixOp(TLAPlusParser.PrefixOpContext ctx) {
        // System.out.println("访问前缀操作符: " + getFullText(ctx));
        return null;
    }


    @Override
    public Void visitPostfixOp(TLAPlusParser.PostfixOpContext ctx) {
        // System.out.println("访问后缀操作符: " + getFullText(ctx));
        return null;
    }

    @Override
    public Void visitInfixOp(TLAPlusParser.InfixOpContext ctx) {
        // System.out.println("访问中缀操作符: " + getFullText(ctx));
        return null;
    }

    // 辅助方法:找到一个节点的所有叶子节点
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
            return ""; // 处理空上下文
        }
        return ctx.getStart().getInputStream()
            .getText(Interval.of(ctx.getStart().getStartIndex(), 
                                ctx.getStop().getStopIndex()));
    }
}


