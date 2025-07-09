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

// Enhanced CFGBuilderVisitor for new grammar design
public class CFGBuilderVisitor extends TLAPlusParserBaseVisitor<Object> {
    private static final String IGNORE_OPERATORS = "^(Init|Next|Spec|TypeOK|TypeInvariant)";
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
        if (ctx.opDecl() != null) {
            for (var id : ctx.opDecl()) {
                constants.add(id.getText());
            }
        }
        return null;
    }

    @Override
    public Void visitVariableDeclaration(TLAPlusParser.VariableDeclarationContext ctx) {
        if (ctx.Identifier() != null) {
            for (var id : ctx.Identifier()) {
                variables.add(id.getText());
            }
        }
        return null;
    }

    @Override
    public Void visitOperatorDefinition(TLAPlusParser.OperatorDefinitionContext ctx) {
        String text = getFullText(ctx);
        Pattern ignorePattern = Pattern.compile(IGNORE_OPERATORS);
        Matcher ignoreMatcher = ignorePattern.matcher(text);

        if (ignoreMatcher.find()) {
            return null;
        }

        String functionName = extractFunctionName(ctx);
        List<String> parameters = extractParameters(ctx);
        
        // Create root node
        CFGStmtNode rootNode = new CFGStmtNode(indentationLevel, "root", null, CFGStmtNode.StmtType.ROOT);
        
        indentationLevel++;
        
        // Visit the body using new grammar rules
        CFGStmtNode bodyNode = visitBody(ctx.body());
        
        if (bodyNode != null) {
            rootNode.addChild(bodyNode);
        }
        
        indentationLevel--;
        
        // Create CFGFuncNode
        CFGFuncNode cfgFuncNode = new CFGFuncNode(functionName, parameters);
        cfgFuncNode.setRoot(rootNode);
        cfgFuncNodes.add(cfgFuncNode);
        
        return null;
    }

    @Override
    public Void visitFunctionDefinition(TLAPlusParser.FunctionDefinitionContext ctx) {
        String functionName = ctx.Identifier().getText();
        List<String> parameters = new ArrayList<>();
        
        // Extract parameters from quantifier bounds
        if (ctx.quantifierBound() != null) {
            for (var bound : ctx.quantifierBound()) {
                parameters.add(bound.getText());
            }
        }

        CFGStmtNode rootNode = new CFGStmtNode(indentationLevel, "root", null, CFGStmtNode.StmtType.ROOT);
        
        indentationLevel++;
        CFGStmtNode bodyNode = visitBody(ctx.body());
        if (bodyNode != null) {
            rootNode.addChild(bodyNode);
        }
        indentationLevel--;
        
        CFGFuncNode cfgFuncNode = new CFGFuncNode(functionName, parameters);
        cfgFuncNode.setRoot(rootNode);
        cfgFuncNodes.add(cfgFuncNode);
        
        return null;
    }

    // Enhanced body visitor: handles junctionItem
    public CFGStmtNode visitBody(TLAPlusParser.BodyContext ctx) {
        indentationLevel++;
        CFGStmtNode result = null;
        
        if (ctx.junctionItem() != null) {
            result = visitJunctionItem(ctx.junctionItem());
        }
        
        indentationLevel--;
        return result;
    }
    
    // New method for visiting logical expressions
    public CFGStmtNode visitLogicalExpression(TLAPlusParser.LogicalExpressionContext ctx) {
        List<TLAPlusParser.LogicalTermContext> terms = ctx.logicalTerm();
        
        if (terms.size() == 1) {
            // Single term, no logical operators
            return visitLogicalTerm(terms.get(0));
        }
        
        // Multiple terms connected by logical operators
        CFGStmtNode firstTerm = visitLogicalTerm(terms.get(0));
        
        List<CFGStmtNode> prevLeaves = new ArrayList<>();
        findLeafNodes(firstTerm, prevLeaves);
        
        for (int i = 1; i < terms.size(); i++) {
            CFGStmtNode termNode = visitLogicalTerm(terms.get(i));
            
            // Connect previous leaves to current term
            for (CFGStmtNode leaf : prevLeaves) {
                leaf.addChild(termNode);
            }
            
            // Update leaves for next iteration
            prevLeaves.clear();
            findLeafNodes(termNode, prevLeaves);
        }
        
        return firstTerm;
    }
    
    // New method for visiting logical terms
    public CFGStmtNode visitLogicalTerm(TLAPlusParser.LogicalTermContext ctx) {
        if (ctx.atomicStatement() != null) {
            return visitAtomicStatement(ctx.atomicStatement());
        } else if (ctx.logicalExpression() != null) {
            // Nested logical expression (parentheses or indented)
            return visitLogicalExpression(ctx.logicalExpression());
        }
        return null;
    }
    
    // Simplified atomic statement visitor
    public CFGStmtNode visitAtomicStatement(TLAPlusParser.AtomicStatementContext ctx) {
        if (ctx.expression() != null) {
            return visitExpression(ctx.expression());
        }
        return null;
    }
    
    // General expression visitor
    public CFGStmtNode visitExpression(TLAPlusParser.ExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }
    
    // Placeholder for structural statements
    public CFGStmtNode visitStructuralStatement(TLAPlusParser.StructuralStatementContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }
    
    // Placeholder for assignment statements  
    public CFGStmtNode visitAssignmentStatement(TLAPlusParser.AssignmentStatementContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }
    
    // Placeholder for predicate expressions
    public CFGStmtNode visitPredicateExpression(TLAPlusParser.PredicateExpressionContext ctx) {
        return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
    }

    // TODO: Future implementation for new grammar rules
    // These methods will be implemented when the new grammar rules are properly integrated
    
    /*
    // New method for visiting logical expressions
    public CFGStmtNode visitLogicalExpression(TLAPlusParser.LogicalExpressionContext ctx) {
        if (ctx.disjunctionExpression() != null) {
            return visitDisjunctionExpression(ctx.disjunctionExpression());
        }
        return null;
    }

    // New method for visiting disjunction expressions (\/)
    public CFGStmtNode visitDisjunctionExpression(TLAPlusParser.DisjunctionExpressionContext ctx) {
        List<TLAPlusParser.ConjunctionExpressionContext> conjunctions = ctx.conjunctionExpression();
        
        if (conjunctions.size() == 1) {
            return visitConjunctionExpression(conjunctions.get(0));
        }
        
        CFGStmtNode firstConj = visitConjunctionExpression(conjunctions.get(0));
        addStrToContentHead(firstConj, "\\/ ");
        
        List<CFGStmtNode> prevLeaves = new ArrayList<>();
        findLeafNodes(firstConj, prevLeaves);
        
        for (int i = 1; i < conjunctions.size(); i++) {
            CFGStmtNode conjNode = visitConjunctionExpression(conjunctions.get(i));
            addStrToContentHead(conjNode, "\\/ ");
            
            for (CFGStmtNode leaf : prevLeaves) {
                leaf.addChild(conjNode);
            }
            
            prevLeaves.clear();
            findLeafNodes(conjNode, prevLeaves);
        }
        
        return firstConj;
    }

    // Additional new grammar methods...
    */

    // Enhanced aobody visitor for new junction list structure
    public CFGStmtNode visitAobody(TLAPlusParser.AobodyContext ctx) {
        if (ctx instanceof TLAPlusParser.JunctionListAobodyContext) {
            return visitJunctionListAobody((TLAPlusParser.JunctionListAobodyContext) ctx);
        } else if (ctx instanceof TLAPlusParser.AobodyStatementContext) {
            return visitAobodyStatement((TLAPlusParser.AobodyStatementContext) ctx);
        } else {
            System.err.println("Unknown aobody context type: " + ctx.getClass().getName());
            return null;
        }
    }

    // New junction list visitor methods
    public CFGStmtNode visitJunctionListAobody(TLAPlusParser.JunctionListAobodyContext ctx) {
        return visitJunctionList(ctx.junctionList());
    }

    public CFGStmtNode visitJunctionList(TLAPlusParser.JunctionListContext ctx) {
        if (ctx instanceof TLAPlusParser.ConjunctionListContext) {
            return visitConjunctionList((TLAPlusParser.ConjunctionListContext) ctx);
        } else if (ctx instanceof TLAPlusParser.DisjunctionListContext) {
            return visitDisjunctionList((TLAPlusParser.DisjunctionListContext) ctx);
        } else if (ctx instanceof TLAPlusParser.StatementListContext) {
            return visitStatementList((TLAPlusParser.StatementListContext) ctx);
        } else {
            // Fallback for unhandled junction list types
            System.err.println("Unknown junction list context type: " + ctx.getClass().getName());
            // Return a simple statement node for now
            return new CFGStmtNode(indentationLevel, getFullText(ctx), ctx, CFGStmtNode.StmtType.NORMAL);
        }
    }

    public CFGStmtNode visitConjunctionList(TLAPlusParser.ConjunctionListContext ctx) {
        List<TLAPlusParser.JunctionItemContext> items = ctx.junctionItem();
        
        CFGStmtNode firstItem = visitJunctionItem(items.get(0));
        addStrToContentHead(firstItem, "/\\ ");
        
        List<CFGStmtNode> prevLeaves = new ArrayList<>();
        findLeafNodes(firstItem, prevLeaves);
        
        for (int i = 1; i < items.size(); i++) {
            CFGStmtNode item = visitJunctionItem(items.get(i));
            addStrToContentHead(item, "/\\ ");
            
            for (CFGStmtNode leaf : prevLeaves) {
                leaf.addChild(item);
            }
            
            prevLeaves.clear();
            findLeafNodes(item, prevLeaves);
        }
        
        return firstItem;
    }

    public CFGStmtNode visitDisjunctionList(TLAPlusParser.DisjunctionListContext ctx) {
        List<TLAPlusParser.JunctionItemContext> items = ctx.junctionItem();
        
        CFGStmtNode firstItem = visitJunctionItem(items.get(0));
        addStrToContentHead(firstItem, "\\/ ");
        
        List<CFGStmtNode> prevLeaves = new ArrayList<>();
        findLeafNodes(firstItem, prevLeaves);
        
        for (int i = 1; i < items.size(); i++) {
            CFGStmtNode item = visitJunctionItem(items.get(i));
            addStrToContentHead(item, "\\/ ");
            
            for (CFGStmtNode leaf : prevLeaves) {
                leaf.addChild(item);
            }
            
            prevLeaves.clear();
            findLeafNodes(item, prevLeaves);
        }
        
        return firstItem;
    }

    public CFGStmtNode visitStatementList(TLAPlusParser.StatementListContext ctx) {
        return visitStatement(ctx.statement());
    }


    public CFGStmtNode visitJunctionItem(TLAPlusParser.JunctionItemContext ctx) {
        if (ctx.statement() != null) {
            return visitStatement(ctx.statement());
        } else if (ctx.junctionList() != null) {
            return visitJunctionList(ctx.junctionList());
        } else {
            System.err.println("Unknown junction item context type");
            return null;
        }
    }

    @Override
    public CFGStmtNode visitAobodyStatement(TLAPlusParser.AobodyStatementContext ctx) {
        return visitStatement(ctx.statement());
    }

    public CFGStmtNode visitStatement(TLAPlusParser.StatementContext ctx) {
        if (ctx.expression() != null && !ctx.expression().isEmpty()) {
            String content = ctx.expression().stream()
                .map(this::getFullText)
                .collect(Collectors.joining(" "));
            return new CFGStmtNode(indentationLevel, content, ctx, CFGStmtNode.StmtType.NORMAL);
        }
        return null;
    }

    // Utility methods
    private String extractFunctionName(TLAPlusParser.OperatorDefinitionContext ctx) {
        if (ctx.nonFixLHS() != null && ctx.nonFixLHS().Identifier() != null && !ctx.nonFixLHS().Identifier().isEmpty()) {
            return ctx.nonFixLHS().Identifier(0).getText();
        }
        return "unknown";
    }

    private List<String> extractParameters(TLAPlusParser.OperatorDefinitionContext ctx) {
        List<String> parameters = new ArrayList<>();
        if (ctx.nonFixLHS() != null && ctx.nonFixLHS().Identifier() != null && ctx.nonFixLHS().Identifier().size() > 1) {
            // Extract parameters from operator definition
            for (int i = 1; i < ctx.nonFixLHS().Identifier().size(); i++) {
                parameters.add(ctx.nonFixLHS().Identifier(i).getText());
            }
        }
        return parameters;
    }

    private String getFullText(ParseTree node) {
        if (node == null) return "";
        return node.getText();
    }

    private void addStrToContentHead(CFGStmtNode node, String prefix) {
        if (node != null) {
            node.setContent(prefix + node.getContent());
        }
    }

    private void findLeafNodes(CFGStmtNode node, List<CFGStmtNode> leaves) {
        if (node == null) return;
        
        if (node.getChildren().isEmpty()) {
            leaves.add(node);
        } else {
            for (CFGStmtNode child : node.getChildren()) {
                findLeafNodes(child, leaves);
            }
        }
    }

    // Placeholder methods for other visitors
    @Override
    public Object visitInstance(TLAPlusParser.InstanceContext ctx) {
        return null;
    }

    @Override
    public Object visitModuleDefinition(TLAPlusParser.ModuleDefinitionContext ctx) {
        return null;
    }

    @Override
    public Object visitAssumption(TLAPlusParser.AssumptionContext ctx) {
        return null;
    }

    @Override
    public Object visitTheorem(TLAPlusParser.TheoremContext ctx) {
        return null;
    }
}