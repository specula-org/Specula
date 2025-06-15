// Generated from TLAPlusParser.g4 by ANTLR 4.13.1

package parser;

import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link TLAPlusParser}.
 */
public interface TLAPlusParserListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#module}.
	 * @param ctx the parse tree
	 */
	void enterModule(TLAPlusParser.ModuleContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#module}.
	 * @param ctx the parse tree
	 */
	void exitModule(TLAPlusParser.ModuleContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#unit}.
	 * @param ctx the parse tree
	 */
	void enterUnit(TLAPlusParser.UnitContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#unit}.
	 * @param ctx the parse tree
	 */
	void exitUnit(TLAPlusParser.UnitContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#variableDeclaration}.
	 * @param ctx the parse tree
	 */
	void enterVariableDeclaration(TLAPlusParser.VariableDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#variableDeclaration}.
	 * @param ctx the parse tree
	 */
	void exitVariableDeclaration(TLAPlusParser.VariableDeclarationContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#constantDeclaration}.
	 * @param ctx the parse tree
	 */
	void enterConstantDeclaration(TLAPlusParser.ConstantDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#constantDeclaration}.
	 * @param ctx the parse tree
	 */
	void exitConstantDeclaration(TLAPlusParser.ConstantDeclarationContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#opDecl}.
	 * @param ctx the parse tree
	 */
	void enterOpDecl(TLAPlusParser.OpDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#opDecl}.
	 * @param ctx the parse tree
	 */
	void exitOpDecl(TLAPlusParser.OpDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#operatorDefinition}.
	 * @param ctx the parse tree
	 */
	void enterOperatorDefinition(TLAPlusParser.OperatorDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#operatorDefinition}.
	 * @param ctx the parse tree
	 */
	void exitOperatorDefinition(TLAPlusParser.OperatorDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#nonFixLHS}.
	 * @param ctx the parse tree
	 */
	void enterNonFixLHS(TLAPlusParser.NonFixLHSContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#nonFixLHS}.
	 * @param ctx the parse tree
	 */
	void exitNonFixLHS(TLAPlusParser.NonFixLHSContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#functionDefinition}.
	 * @param ctx the parse tree
	 */
	void enterFunctionDefinition(TLAPlusParser.FunctionDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#functionDefinition}.
	 * @param ctx the parse tree
	 */
	void exitFunctionDefinition(TLAPlusParser.FunctionDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#quantifierBound}.
	 * @param ctx the parse tree
	 */
	void enterQuantifierBound(TLAPlusParser.QuantifierBoundContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#quantifierBound}.
	 * @param ctx the parse tree
	 */
	void exitQuantifierBound(TLAPlusParser.QuantifierBoundContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#instance}.
	 * @param ctx the parse tree
	 */
	void enterInstance(TLAPlusParser.InstanceContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#instance}.
	 * @param ctx the parse tree
	 */
	void exitInstance(TLAPlusParser.InstanceContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#substitution}.
	 * @param ctx the parse tree
	 */
	void enterSubstitution(TLAPlusParser.SubstitutionContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#substitution}.
	 * @param ctx the parse tree
	 */
	void exitSubstitution(TLAPlusParser.SubstitutionContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#argument}.
	 * @param ctx the parse tree
	 */
	void enterArgument(TLAPlusParser.ArgumentContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#argument}.
	 * @param ctx the parse tree
	 */
	void exitArgument(TLAPlusParser.ArgumentContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#instancePrefix}.
	 * @param ctx the parse tree
	 */
	void enterInstancePrefix(TLAPlusParser.InstancePrefixContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#instancePrefix}.
	 * @param ctx the parse tree
	 */
	void exitInstancePrefix(TLAPlusParser.InstancePrefixContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#generalIdentifier}.
	 * @param ctx the parse tree
	 */
	void enterGeneralIdentifier(TLAPlusParser.GeneralIdentifierContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#generalIdentifier}.
	 * @param ctx the parse tree
	 */
	void exitGeneralIdentifier(TLAPlusParser.GeneralIdentifierContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#generalPrefixOp}.
	 * @param ctx the parse tree
	 */
	void enterGeneralPrefixOp(TLAPlusParser.GeneralPrefixOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#generalPrefixOp}.
	 * @param ctx the parse tree
	 */
	void exitGeneralPrefixOp(TLAPlusParser.GeneralPrefixOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#generalInfixOp}.
	 * @param ctx the parse tree
	 */
	void enterGeneralInfixOp(TLAPlusParser.GeneralInfixOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#generalInfixOp}.
	 * @param ctx the parse tree
	 */
	void exitGeneralInfixOp(TLAPlusParser.GeneralInfixOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#generalPostfixOp}.
	 * @param ctx the parse tree
	 */
	void enterGeneralPostfixOp(TLAPlusParser.GeneralPostfixOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#generalPostfixOp}.
	 * @param ctx the parse tree
	 */
	void exitGeneralPostfixOp(TLAPlusParser.GeneralPostfixOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#moduleDefinition}.
	 * @param ctx the parse tree
	 */
	void enterModuleDefinition(TLAPlusParser.ModuleDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#moduleDefinition}.
	 * @param ctx the parse tree
	 */
	void exitModuleDefinition(TLAPlusParser.ModuleDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#assumption}.
	 * @param ctx the parse tree
	 */
	void enterAssumption(TLAPlusParser.AssumptionContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#assumption}.
	 * @param ctx the parse tree
	 */
	void exitAssumption(TLAPlusParser.AssumptionContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#theorem}.
	 * @param ctx the parse tree
	 */
	void enterTheorem(TLAPlusParser.TheoremContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#theorem}.
	 * @param ctx the parse tree
	 */
	void exitTheorem(TLAPlusParser.TheoremContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#rightExpression}.
	 * @param ctx the parse tree
	 */
	void enterRightExpression(TLAPlusParser.RightExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#rightExpression}.
	 * @param ctx the parse tree
	 */
	void exitRightExpression(TLAPlusParser.RightExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code FunctionCall}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterFunctionCall(TLAPlusParser.FunctionCallContext ctx);
	/**
	 * Exit a parse tree produced by the {@code FunctionCall}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitFunctionCall(TLAPlusParser.FunctionCallContext ctx);
	/**
	 * Enter a parse tree produced by the {@code PrefixOperation}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterPrefixOperation(TLAPlusParser.PrefixOperationContext ctx);
	/**
	 * Exit a parse tree produced by the {@code PrefixOperation}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitPrefixOperation(TLAPlusParser.PrefixOperationContext ctx);
	/**
	 * Enter a parse tree produced by the {@code IdentifierExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterIdentifierExpression(TLAPlusParser.IdentifierExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code IdentifierExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitIdentifierExpression(TLAPlusParser.IdentifierExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ParenthesizedExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterParenthesizedExpression(TLAPlusParser.ParenthesizedExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ParenthesizedExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitParenthesizedExpression(TLAPlusParser.ParenthesizedExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code QuantifierExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterQuantifierExpression(TLAPlusParser.QuantifierExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code QuantifierExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitQuantifierExpression(TLAPlusParser.QuantifierExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code SimpleQuantifierExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterSimpleQuantifierExpression(TLAPlusParser.SimpleQuantifierExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code SimpleQuantifierExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitSimpleQuantifierExpression(TLAPlusParser.SimpleQuantifierExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ChooseExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterChooseExpression(TLAPlusParser.ChooseExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ChooseExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitChooseExpression(TLAPlusParser.ChooseExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ChooseInExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterChooseInExpression(TLAPlusParser.ChooseInExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ChooseInExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitChooseInExpression(TLAPlusParser.ChooseInExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code EmptySet}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterEmptySet(TLAPlusParser.EmptySetContext ctx);
	/**
	 * Exit a parse tree produced by the {@code EmptySet}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitEmptySet(TLAPlusParser.EmptySetContext ctx);
	/**
	 * Enter a parse tree produced by the {@code SetExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterSetExpression(TLAPlusParser.SetExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code SetExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitSetExpression(TLAPlusParser.SetExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code SetComprehension}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterSetComprehension(TLAPlusParser.SetComprehensionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code SetComprehension}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitSetComprehension(TLAPlusParser.SetComprehensionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code SetQuantifier}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterSetQuantifier(TLAPlusParser.SetQuantifierContext ctx);
	/**
	 * Exit a parse tree produced by the {@code SetQuantifier}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitSetQuantifier(TLAPlusParser.SetQuantifierContext ctx);
	/**
	 * Enter a parse tree produced by the {@code MappingExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterMappingExpression(TLAPlusParser.MappingExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code MappingExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitMappingExpression(TLAPlusParser.MappingExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ArrowExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterArrowExpression(TLAPlusParser.ArrowExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ArrowExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitArrowExpression(TLAPlusParser.ArrowExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code MapstoExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterMapstoExpression(TLAPlusParser.MapstoExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code MapstoExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitMapstoExpression(TLAPlusParser.MapstoExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ColonExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterColonExpression(TLAPlusParser.ColonExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ColonExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitColonExpression(TLAPlusParser.ColonExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ExceptExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExceptExpression(TLAPlusParser.ExceptExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ExceptExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExceptExpression(TLAPlusParser.ExceptExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code DoubleLessExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterDoubleLessExpression(TLAPlusParser.DoubleLessExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code DoubleLessExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitDoubleLessExpression(TLAPlusParser.DoubleLessExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BracketUnderscoreExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterBracketUnderscoreExpression(TLAPlusParser.BracketUnderscoreExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BracketUnderscoreExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitBracketUnderscoreExpression(TLAPlusParser.BracketUnderscoreExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code DoubleLessUnderscoreExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterDoubleLessUnderscoreExpression(TLAPlusParser.DoubleLessUnderscoreExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code DoubleLessUnderscoreExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitDoubleLessUnderscoreExpression(TLAPlusParser.DoubleLessUnderscoreExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code FairnessExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterFairnessExpression(TLAPlusParser.FairnessExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code FairnessExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitFairnessExpression(TLAPlusParser.FairnessExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code IfExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterIfExpression(TLAPlusParser.IfExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code IfExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitIfExpression(TLAPlusParser.IfExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code CaseExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterCaseExpression(TLAPlusParser.CaseExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code CaseExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitCaseExpression(TLAPlusParser.CaseExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code LetExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterLetExpression(TLAPlusParser.LetExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code LetExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitLetExpression(TLAPlusParser.LetExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code SlashBackslashExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterSlashBackslashExpression(TLAPlusParser.SlashBackslashExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code SlashBackslashExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitSlashBackslashExpression(TLAPlusParser.SlashBackslashExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BackslashSlashExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterBackslashSlashExpression(TLAPlusParser.BackslashSlashExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BackslashSlashExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitBackslashSlashExpression(TLAPlusParser.BackslashSlashExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code NumberExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterNumberExpression(TLAPlusParser.NumberExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code NumberExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitNumberExpression(TLAPlusParser.NumberExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code StringExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterStringExpression(TLAPlusParser.StringExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code StringExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitStringExpression(TLAPlusParser.StringExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code AtExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterAtExpression(TLAPlusParser.AtExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code AtExpression}
	 * labeled alternative in {@link TLAPlusParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitAtExpression(TLAPlusParser.AtExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#thenExpression}.
	 * @param ctx the parse tree
	 */
	void enterThenExpression(TLAPlusParser.ThenExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#thenExpression}.
	 * @param ctx the parse tree
	 */
	void exitThenExpression(TLAPlusParser.ThenExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#elseExpression}.
	 * @param ctx the parse tree
	 */
	void enterElseExpression(TLAPlusParser.ElseExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#elseExpression}.
	 * @param ctx the parse tree
	 */
	void exitElseExpression(TLAPlusParser.ElseExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#identifierOrTuple}.
	 * @param ctx the parse tree
	 */
	void enterIdentifierOrTuple(TLAPlusParser.IdentifierOrTupleContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#identifierOrTuple}.
	 * @param ctx the parse tree
	 */
	void exitIdentifierOrTuple(TLAPlusParser.IdentifierOrTupleContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#reservedWord}.
	 * @param ctx the parse tree
	 */
	void enterReservedWord(TLAPlusParser.ReservedWordContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#reservedWord}.
	 * @param ctx the parse tree
	 */
	void exitReservedWord(TLAPlusParser.ReservedWordContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#prefixOp}.
	 * @param ctx the parse tree
	 */
	void enterPrefixOp(TLAPlusParser.PrefixOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#prefixOp}.
	 * @param ctx the parse tree
	 */
	void exitPrefixOp(TLAPlusParser.PrefixOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#infixOp}.
	 * @param ctx the parse tree
	 */
	void enterInfixOp(TLAPlusParser.InfixOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#infixOp}.
	 * @param ctx the parse tree
	 */
	void exitInfixOp(TLAPlusParser.InfixOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#postfixOp}.
	 * @param ctx the parse tree
	 */
	void enterPostfixOp(TLAPlusParser.PostfixOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#postfixOp}.
	 * @param ctx the parse tree
	 */
	void exitPostfixOp(TLAPlusParser.PostfixOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#body}.
	 * @param ctx the parse tree
	 */
	void enterBody(TLAPlusParser.BodyContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#body}.
	 * @param ctx the parse tree
	 */
	void exitBody(TLAPlusParser.BodyContext ctx);
	/**
	 * Enter a parse tree produced by the {@code nonindentedSlashBackslash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 */
	void enterNonindentedSlashBackslash(TLAPlusParser.NonindentedSlashBackslashContext ctx);
	/**
	 * Exit a parse tree produced by the {@code nonindentedSlashBackslash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 */
	void exitNonindentedSlashBackslash(TLAPlusParser.NonindentedSlashBackslashContext ctx);
	/**
	 * Enter a parse tree produced by the {@code nonindentedBackslashSlash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 */
	void enterNonindentedBackslashSlash(TLAPlusParser.NonindentedBackslashSlashContext ctx);
	/**
	 * Exit a parse tree produced by the {@code nonindentedBackslashSlash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 */
	void exitNonindentedBackslashSlash(TLAPlusParser.NonindentedBackslashSlashContext ctx);
	/**
	 * Enter a parse tree produced by the {@code indentedSlashBackslash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 */
	void enterIndentedSlashBackslash(TLAPlusParser.IndentedSlashBackslashContext ctx);
	/**
	 * Exit a parse tree produced by the {@code indentedSlashBackslash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 */
	void exitIndentedSlashBackslash(TLAPlusParser.IndentedSlashBackslashContext ctx);
	/**
	 * Enter a parse tree produced by the {@code indentedBackslashSlash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 */
	void enterIndentedBackslashSlash(TLAPlusParser.IndentedBackslashSlashContext ctx);
	/**
	 * Exit a parse tree produced by the {@code indentedBackslashSlash}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 */
	void exitIndentedBackslashSlash(TLAPlusParser.IndentedBackslashSlashContext ctx);
	/**
	 * Enter a parse tree produced by the {@code aobodyStatement}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 */
	void enterAobodyStatement(TLAPlusParser.AobodyStatementContext ctx);
	/**
	 * Exit a parse tree produced by the {@code aobodyStatement}
	 * labeled alternative in {@link TLAPlusParser#aobody}.
	 * @param ctx the parse tree
	 */
	void exitAobodyStatement(TLAPlusParser.AobodyStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link TLAPlusParser#statement}.
	 * @param ctx the parse tree
	 */
	void enterStatement(TLAPlusParser.StatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link TLAPlusParser#statement}.
	 * @param ctx the parse tree
	 */
	void exitStatement(TLAPlusParser.StatementContext ctx);
}