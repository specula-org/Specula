// Generated from TLAPlusParser.g4 by ANTLR 4.13.1

package parser;

import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link TLAPlusParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface TLAPlusParserVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#module}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitModule(TLAPlusParser.ModuleContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#unit}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUnit(TLAPlusParser.UnitContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#variableDeclaration}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVariableDeclaration(TLAPlusParser.VariableDeclarationContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#constantDeclaration}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConstantDeclaration(TLAPlusParser.ConstantDeclarationContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#opDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOpDecl(TLAPlusParser.OpDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#operatorDefinition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOperatorDefinition(TLAPlusParser.OperatorDefinitionContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#nonFixLHS}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNonFixLHS(TLAPlusParser.NonFixLHSContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#functionDefinition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunctionDefinition(TLAPlusParser.FunctionDefinitionContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#quantifierBound}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuantifierBound(TLAPlusParser.QuantifierBoundContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#instance}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInstance(TLAPlusParser.InstanceContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#substitution}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSubstitution(TLAPlusParser.SubstitutionContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#argument}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArgument(TLAPlusParser.ArgumentContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#instancePrefix}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInstancePrefix(TLAPlusParser.InstancePrefixContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#generalIdentifier}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeneralIdentifier(TLAPlusParser.GeneralIdentifierContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#generalPrefixOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeneralPrefixOp(TLAPlusParser.GeneralPrefixOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#generalInfixOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeneralInfixOp(TLAPlusParser.GeneralInfixOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#generalPostfixOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeneralPostfixOp(TLAPlusParser.GeneralPostfixOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#moduleDefinition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitModuleDefinition(TLAPlusParser.ModuleDefinitionContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#assumption}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssumption(TLAPlusParser.AssumptionContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#theorem}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheorem(TLAPlusParser.TheoremContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#rightExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRightExpression(TLAPlusParser.RightExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code FunctionCall}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunctionCall(TLAPlusParser.FunctionCallContext ctx);
	/**
	 * Visit a parse tree produced by the {@code PrefixOperation}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrefixOperation(TLAPlusParser.PrefixOperationContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IdentifierExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdentifierExpression(TLAPlusParser.IdentifierExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ParenthesizedExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenthesizedExpression(TLAPlusParser.ParenthesizedExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code QuantifierExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuantifierExpression(TLAPlusParser.QuantifierExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code SimpleQuantifierExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSimpleQuantifierExpression(TLAPlusParser.SimpleQuantifierExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ChooseExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitChooseExpression(TLAPlusParser.ChooseExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ChooseInExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitChooseInExpression(TLAPlusParser.ChooseInExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code EmptySet}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEmptySet(TLAPlusParser.EmptySetContext ctx);
	/**
	 * Visit a parse tree produced by the {@code SetExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSetExpression(TLAPlusParser.SetExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code SetComprehension}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSetComprehension(TLAPlusParser.SetComprehensionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code SetQuantifier}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSetQuantifier(TLAPlusParser.SetQuantifierContext ctx);
	/**
	 * Visit a parse tree produced by the {@code MappingExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMappingExpression(TLAPlusParser.MappingExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ArrowExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrowExpression(TLAPlusParser.ArrowExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code MapstoExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMapstoExpression(TLAPlusParser.MapstoExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ColonExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitColonExpression(TLAPlusParser.ColonExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ExceptExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExceptExpression(TLAPlusParser.ExceptExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code DoubleLessExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDoubleLessExpression(TLAPlusParser.DoubleLessExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BracketUnderscoreExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBracketUnderscoreExpression(TLAPlusParser.BracketUnderscoreExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code DoubleLessUnderscoreExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDoubleLessUnderscoreExpression(TLAPlusParser.DoubleLessUnderscoreExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code FairnessExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFairnessExpression(TLAPlusParser.FairnessExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IfExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIfExpression(TLAPlusParser.IfExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code CaseExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCaseExpression(TLAPlusParser.CaseExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code LetExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLetExpression(TLAPlusParser.LetExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code SlashBackslashExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSlashBackslashExpression(TLAPlusParser.SlashBackslashExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BackslashSlashExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBackslashSlashExpression(TLAPlusParser.BackslashSlashExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code NumberExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNumberExpression(TLAPlusParser.NumberExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code StringExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStringExpression(TLAPlusParser.StringExpressionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code AtExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAtExpression(TLAPlusParser.AtExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#thenExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitThenExpression(TLAPlusParser.ThenExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#elseExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitElseExpression(TLAPlusParser.ElseExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#identifierOrTuple}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdentifierOrTuple(TLAPlusParser.IdentifierOrTupleContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#reservedWord}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitReservedWord(TLAPlusParser.ReservedWordContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#prefixOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrefixOp(TLAPlusParser.PrefixOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#infixOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfixOp(TLAPlusParser.InfixOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#postfixOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPostfixOp(TLAPlusParser.PostfixOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#body}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBody(TLAPlusParser.BodyContext ctx);
	/**
	 * Visit a parse tree produced by the {@code nonindentedSlashBackslash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNonindentedSlashBackslash(TLAPlusParser.NonindentedSlashBackslashContext ctx);
	/**
	 * Visit a parse tree produced by the {@code nonindentedBackslashSlash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNonindentedBackslashSlash(TLAPlusParser.NonindentedBackslashSlashContext ctx);
	/**
	 * Visit a parse tree produced by the {@code indentedSlashBackslash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIndentedSlashBackslash(TLAPlusParser.IndentedSlashBackslashContext ctx);
	/**
	 * Visit a parse tree produced by the {@code indentedBackslashSlash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIndentedBackslashSlash(TLAPlusParser.IndentedBackslashSlashContext ctx);
	/**
	 * Visit a parse tree produced by the {@code aobodyStatement}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAobodyStatement(TLAPlusParser.AobodyStatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link TLAPlusParser#statement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStatement(TLAPlusParser.StatementContext ctx);
}