// Generated from SimpleC.g by ANTLR 4.5.1
package parser;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SimpleCParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.5.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		T__17=18, T__18=19, T__19=20, T__20=21, T__21=22, T__22=23, T__23=24, 
		T__24=25, T__25=26, T__26=27, T__27=28, T__28=29, T__29=30, T__30=31, 
		T__31=32, T__32=33, T__33=34, T__34=35, T__35=36, T__36=37, T__37=38, 
		T__38=39, T__39=40, T__40=41, T__41=42, T__42=43, T__43=44, T__44=45, 
		ID=46, NUMBER=47, PLUSPLUS=48, MINUSMINUS=49, COMMENT=50, WS=51;
	public static final int
		RULE_program = 0, RULE_varDecl = 1, RULE_procedureDecl = 2, RULE_formalParam = 3, 
		RULE_prepost = 4, RULE_requires = 5, RULE_ensures = 6, RULE_candidateRequires = 7, 
		RULE_candidateEnsures = 8, RULE_stmt = 9, RULE_assignStmt = 10, RULE_assertStmt = 11, 
		RULE_assumeStmt = 12, RULE_havocStmt = 13, RULE_callStmt = 14, RULE_ifStmt = 15, 
		RULE_whileStmt = 16, RULE_blockStmt = 17, RULE_loopInvariant = 18, RULE_invariant = 19, 
		RULE_candidateInvariant = 20, RULE_expr = 21, RULE_ternExpr = 22, RULE_lorExpr = 23, 
		RULE_landExpr = 24, RULE_borExpr = 25, RULE_bxorExpr = 26, RULE_bandExpr = 27, 
		RULE_equalityExpr = 28, RULE_relExpr = 29, RULE_shiftExpr = 30, RULE_addExpr = 31, 
		RULE_mulExpr = 32, RULE_unaryExpr = 33, RULE_atomExpr = 34, RULE_numberExpr = 35, 
		RULE_varrefExpr = 36, RULE_parenExpr = 37, RULE_resultExpr = 38, RULE_oldExpr = 39, 
		RULE_varref = 40, RULE_varIdentifier = 41;
	public static final String[] ruleNames = {
		"program", "varDecl", "procedureDecl", "formalParam", "prepost", "requires", 
		"ensures", "candidateRequires", "candidateEnsures", "stmt", "assignStmt", 
		"assertStmt", "assumeStmt", "havocStmt", "callStmt", "ifStmt", "whileStmt", 
		"blockStmt", "loopInvariant", "invariant", "candidateInvariant", "expr", 
		"ternExpr", "lorExpr", "landExpr", "borExpr", "bxorExpr", "bandExpr", 
		"equalityExpr", "relExpr", "shiftExpr", "addExpr", "mulExpr", "unaryExpr", 
		"atomExpr", "numberExpr", "varrefExpr", "parenExpr", "resultExpr", "oldExpr", 
		"varref", "varIdentifier"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "'int'", "';'", "'('", "','", "')'", "'{'", "'return'", "'}'", "'requires'", 
		"'ensures'", "'candidate_requires'", "'candidate_ensures'", "'='", "'assert'", 
		"'assume'", "'havoc'", "'if'", "'else'", "'while'", "'invariant'", "'candidate_invariant'", 
		"'?'", "':'", "'||'", "'&&'", "'|'", "'^'", "'&'", "'=='", "'!='", "'<'", 
		"'<='", "'>'", "'>='", "'<<'", "'>>'", "'+'", "'-'", "'*'", "'/'", "'%'", 
		"'!'", "'~'", "'\\result'", "'\\old'", null, null, "'++'", "'--'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, null, null, null, null, null, "ID", "NUMBER", 
		"PLUSPLUS", "MINUSMINUS", "COMMENT", "WS"
	};
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "SimpleC.g"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public SimpleCParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}
	public static class ProgramContext extends ParserRuleContext {
		public VarDeclContext varDecl;
		public List<VarDeclContext> globals = new ArrayList<VarDeclContext>();
		public ProcedureDeclContext procedureDecl;
		public List<ProcedureDeclContext> procedures = new ArrayList<ProcedureDeclContext>();
		public List<VarDeclContext> varDecl() {
			return getRuleContexts(VarDeclContext.class);
		}
		public VarDeclContext varDecl(int i) {
			return getRuleContext(VarDeclContext.class,i);
		}
		public List<ProcedureDeclContext> procedureDecl() {
			return getRuleContexts(ProcedureDeclContext.class);
		}
		public ProcedureDeclContext procedureDecl(int i) {
			return getRuleContext(ProcedureDeclContext.class,i);
		}
		public ProgramContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_program; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterProgram(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitProgram(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitProgram(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ProgramContext program() throws RecognitionException {
		ProgramContext _localctx = new ProgramContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_program);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(87);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,0,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(84);
					((ProgramContext)_localctx).varDecl = varDecl();
					((ProgramContext)_localctx).globals.add(((ProgramContext)_localctx).varDecl);
					}
					} 
				}
				setState(89);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,0,_ctx);
			}
			setState(93);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(90);
				((ProgramContext)_localctx).procedureDecl = procedureDecl();
				((ProgramContext)_localctx).procedures.add(((ProgramContext)_localctx).procedureDecl);
				}
				}
				setState(95);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VarDeclContext extends ParserRuleContext {
		public VarIdentifierContext ident;
		public VarIdentifierContext varIdentifier() {
			return getRuleContext(VarIdentifierContext.class,0);
		}
		public VarDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterVarDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitVarDecl(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitVarDecl(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarDeclContext varDecl() throws RecognitionException {
		VarDeclContext _localctx = new VarDeclContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_varDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(96);
			match(T__0);
			setState(97);
			((VarDeclContext)_localctx).ident = varIdentifier();
			setState(98);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ProcedureDeclContext extends ParserRuleContext {
		public Token name;
		public FormalParamContext formalParam;
		public List<FormalParamContext> formals = new ArrayList<FormalParamContext>();
		public PrepostContext prepost;
		public List<PrepostContext> contract = new ArrayList<PrepostContext>();
		public StmtContext stmt;
		public List<StmtContext> stmts = new ArrayList<StmtContext>();
		public ExprContext returnExpr;
		public TerminalNode ID() { return getToken(SimpleCParser.ID, 0); }
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public List<FormalParamContext> formalParam() {
			return getRuleContexts(FormalParamContext.class);
		}
		public FormalParamContext formalParam(int i) {
			return getRuleContext(FormalParamContext.class,i);
		}
		public List<PrepostContext> prepost() {
			return getRuleContexts(PrepostContext.class);
		}
		public PrepostContext prepost(int i) {
			return getRuleContext(PrepostContext.class,i);
		}
		public List<StmtContext> stmt() {
			return getRuleContexts(StmtContext.class);
		}
		public StmtContext stmt(int i) {
			return getRuleContext(StmtContext.class,i);
		}
		public ProcedureDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_procedureDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterProcedureDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitProcedureDecl(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitProcedureDecl(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ProcedureDeclContext procedureDecl() throws RecognitionException {
		ProcedureDeclContext _localctx = new ProcedureDeclContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_procedureDecl);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(100);
			match(T__0);
			setState(101);
			((ProcedureDeclContext)_localctx).name = match(ID);
			setState(102);
			match(T__2);
			setState(111);
			_la = _input.LA(1);
			if (_la==T__0) {
				{
				setState(103);
				((ProcedureDeclContext)_localctx).formalParam = formalParam();
				((ProcedureDeclContext)_localctx).formals.add(((ProcedureDeclContext)_localctx).formalParam);
				setState(108);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__3) {
					{
					{
					setState(104);
					match(T__3);
					setState(105);
					((ProcedureDeclContext)_localctx).formalParam = formalParam();
					((ProcedureDeclContext)_localctx).formals.add(((ProcedureDeclContext)_localctx).formalParam);
					}
					}
					setState(110);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(113);
			match(T__4);
			setState(122);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__8) | (1L << T__9) | (1L << T__10) | (1L << T__11))) != 0)) {
				{
				setState(114);
				((ProcedureDeclContext)_localctx).prepost = prepost();
				((ProcedureDeclContext)_localctx).contract.add(((ProcedureDeclContext)_localctx).prepost);
				setState(119);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__3) {
					{
					{
					setState(115);
					match(T__3);
					setState(116);
					((ProcedureDeclContext)_localctx).prepost = prepost();
					((ProcedureDeclContext)_localctx).contract.add(((ProcedureDeclContext)_localctx).prepost);
					}
					}
					setState(121);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(124);
			match(T__5);
			setState(128);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__0) | (1L << T__5) | (1L << T__13) | (1L << T__14) | (1L << T__15) | (1L << T__16) | (1L << T__18) | (1L << ID))) != 0)) {
				{
				{
				setState(125);
				((ProcedureDeclContext)_localctx).stmt = stmt();
				((ProcedureDeclContext)_localctx).stmts.add(((ProcedureDeclContext)_localctx).stmt);
				}
				}
				setState(130);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(131);
			match(T__6);
			setState(132);
			((ProcedureDeclContext)_localctx).returnExpr = expr();
			setState(133);
			match(T__1);
			setState(134);
			match(T__7);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FormalParamContext extends ParserRuleContext {
		public VarIdentifierContext ident;
		public VarIdentifierContext varIdentifier() {
			return getRuleContext(VarIdentifierContext.class,0);
		}
		public FormalParamContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_formalParam; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterFormalParam(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitFormalParam(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitFormalParam(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FormalParamContext formalParam() throws RecognitionException {
		FormalParamContext _localctx = new FormalParamContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_formalParam);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(136);
			match(T__0);
			setState(137);
			((FormalParamContext)_localctx).ident = varIdentifier();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class PrepostContext extends ParserRuleContext {
		public RequiresContext requires() {
			return getRuleContext(RequiresContext.class,0);
		}
		public EnsuresContext ensures() {
			return getRuleContext(EnsuresContext.class,0);
		}
		public CandidateRequiresContext candidateRequires() {
			return getRuleContext(CandidateRequiresContext.class,0);
		}
		public CandidateEnsuresContext candidateEnsures() {
			return getRuleContext(CandidateEnsuresContext.class,0);
		}
		public PrepostContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_prepost; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterPrepost(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitPrepost(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitPrepost(this);
			else return visitor.visitChildren(this);
		}
	}

	public final PrepostContext prepost() throws RecognitionException {
		PrepostContext _localctx = new PrepostContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_prepost);
		try {
			setState(143);
			switch (_input.LA(1)) {
			case T__8:
				enterOuterAlt(_localctx, 1);
				{
				setState(139);
				requires();
				}
				break;
			case T__9:
				enterOuterAlt(_localctx, 2);
				{
				setState(140);
				ensures();
				}
				break;
			case T__10:
				enterOuterAlt(_localctx, 3);
				{
				setState(141);
				candidateRequires();
				}
				break;
			case T__11:
				enterOuterAlt(_localctx, 4);
				{
				setState(142);
				candidateEnsures();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class RequiresContext extends ParserRuleContext {
		public ExprContext condition;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public RequiresContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_requires; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterRequires(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitRequires(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitRequires(this);
			else return visitor.visitChildren(this);
		}
	}

	public final RequiresContext requires() throws RecognitionException {
		RequiresContext _localctx = new RequiresContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_requires);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(145);
			match(T__8);
			setState(146);
			((RequiresContext)_localctx).condition = expr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EnsuresContext extends ParserRuleContext {
		public ExprContext condition;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public EnsuresContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ensures; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterEnsures(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitEnsures(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitEnsures(this);
			else return visitor.visitChildren(this);
		}
	}

	public final EnsuresContext ensures() throws RecognitionException {
		EnsuresContext _localctx = new EnsuresContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_ensures);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(148);
			match(T__9);
			setState(149);
			((EnsuresContext)_localctx).condition = expr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class CandidateRequiresContext extends ParserRuleContext {
		public ExprContext condition;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public CandidateRequiresContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_candidateRequires; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterCandidateRequires(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitCandidateRequires(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitCandidateRequires(this);
			else return visitor.visitChildren(this);
		}
	}

	public final CandidateRequiresContext candidateRequires() throws RecognitionException {
		CandidateRequiresContext _localctx = new CandidateRequiresContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_candidateRequires);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(151);
			match(T__10);
			setState(152);
			((CandidateRequiresContext)_localctx).condition = expr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class CandidateEnsuresContext extends ParserRuleContext {
		public ExprContext condition;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public CandidateEnsuresContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_candidateEnsures; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterCandidateEnsures(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitCandidateEnsures(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitCandidateEnsures(this);
			else return visitor.visitChildren(this);
		}
	}

	public final CandidateEnsuresContext candidateEnsures() throws RecognitionException {
		CandidateEnsuresContext _localctx = new CandidateEnsuresContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_candidateEnsures);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(154);
			match(T__11);
			setState(155);
			((CandidateEnsuresContext)_localctx).condition = expr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StmtContext extends ParserRuleContext {
		public VarDeclContext varDecl() {
			return getRuleContext(VarDeclContext.class,0);
		}
		public AssignStmtContext assignStmt() {
			return getRuleContext(AssignStmtContext.class,0);
		}
		public AssertStmtContext assertStmt() {
			return getRuleContext(AssertStmtContext.class,0);
		}
		public AssumeStmtContext assumeStmt() {
			return getRuleContext(AssumeStmtContext.class,0);
		}
		public HavocStmtContext havocStmt() {
			return getRuleContext(HavocStmtContext.class,0);
		}
		public CallStmtContext callStmt() {
			return getRuleContext(CallStmtContext.class,0);
		}
		public IfStmtContext ifStmt() {
			return getRuleContext(IfStmtContext.class,0);
		}
		public WhileStmtContext whileStmt() {
			return getRuleContext(WhileStmtContext.class,0);
		}
		public BlockStmtContext blockStmt() {
			return getRuleContext(BlockStmtContext.class,0);
		}
		public StmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_stmt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitStmt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final StmtContext stmt() throws RecognitionException {
		StmtContext _localctx = new StmtContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_stmt);
		try {
			setState(166);
			switch ( getInterpreter().adaptivePredict(_input,8,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(157);
				varDecl();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(158);
				assignStmt();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(159);
				assertStmt();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(160);
				assumeStmt();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(161);
				havocStmt();
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(162);
				callStmt();
				}
				break;
			case 7:
				enterOuterAlt(_localctx, 7);
				{
				setState(163);
				ifStmt();
				}
				break;
			case 8:
				enterOuterAlt(_localctx, 8);
				{
				setState(164);
				whileStmt();
				}
				break;
			case 9:
				enterOuterAlt(_localctx, 9);
				{
				setState(165);
				blockStmt();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssignStmtContext extends ParserRuleContext {
		public VarrefContext lhs;
		public ExprContext rhs;
		public VarrefContext varref() {
			return getRuleContext(VarrefContext.class,0);
		}
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public AssignStmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assignStmt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterAssignStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitAssignStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitAssignStmt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssignStmtContext assignStmt() throws RecognitionException {
		AssignStmtContext _localctx = new AssignStmtContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_assignStmt);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(168);
			((AssignStmtContext)_localctx).lhs = varref();
			setState(169);
			match(T__12);
			setState(170);
			((AssignStmtContext)_localctx).rhs = expr();
			setState(171);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertStmtContext extends ParserRuleContext {
		public ExprContext condition;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public AssertStmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertStmt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterAssertStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitAssertStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitAssertStmt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertStmtContext assertStmt() throws RecognitionException {
		AssertStmtContext _localctx = new AssertStmtContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_assertStmt);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(173);
			match(T__13);
			setState(174);
			((AssertStmtContext)_localctx).condition = expr();
			setState(175);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssumeStmtContext extends ParserRuleContext {
		public ExprContext condition;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public AssumeStmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assumeStmt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterAssumeStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitAssumeStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitAssumeStmt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssumeStmtContext assumeStmt() throws RecognitionException {
		AssumeStmtContext _localctx = new AssumeStmtContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_assumeStmt);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(177);
			match(T__14);
			setState(178);
			((AssumeStmtContext)_localctx).condition = expr();
			setState(179);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class HavocStmtContext extends ParserRuleContext {
		public VarrefContext var;
		public VarrefContext varref() {
			return getRuleContext(VarrefContext.class,0);
		}
		public HavocStmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_havocStmt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterHavocStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitHavocStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitHavocStmt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final HavocStmtContext havocStmt() throws RecognitionException {
		HavocStmtContext _localctx = new HavocStmtContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_havocStmt);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(181);
			match(T__15);
			setState(182);
			((HavocStmtContext)_localctx).var = varref();
			setState(183);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class CallStmtContext extends ParserRuleContext {
		public VarrefContext lhs;
		public Token callee;
		public ExprContext expr;
		public List<ExprContext> actuals = new ArrayList<ExprContext>();
		public VarrefContext varref() {
			return getRuleContext(VarrefContext.class,0);
		}
		public TerminalNode ID() { return getToken(SimpleCParser.ID, 0); }
		public List<ExprContext> expr() {
			return getRuleContexts(ExprContext.class);
		}
		public ExprContext expr(int i) {
			return getRuleContext(ExprContext.class,i);
		}
		public CallStmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_callStmt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterCallStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitCallStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitCallStmt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final CallStmtContext callStmt() throws RecognitionException {
		CallStmtContext _localctx = new CallStmtContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_callStmt);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(185);
			((CallStmtContext)_localctx).lhs = varref();
			setState(186);
			match(T__12);
			setState(187);
			((CallStmtContext)_localctx).callee = match(ID);
			setState(188);
			match(T__2);
			setState(197);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__2) | (1L << T__36) | (1L << T__37) | (1L << T__41) | (1L << T__42) | (1L << T__43) | (1L << T__44) | (1L << ID) | (1L << NUMBER))) != 0)) {
				{
				setState(189);
				((CallStmtContext)_localctx).expr = expr();
				((CallStmtContext)_localctx).actuals.add(((CallStmtContext)_localctx).expr);
				setState(194);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__3) {
					{
					{
					setState(190);
					match(T__3);
					setState(191);
					((CallStmtContext)_localctx).expr = expr();
					((CallStmtContext)_localctx).actuals.add(((CallStmtContext)_localctx).expr);
					}
					}
					setState(196);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(199);
			match(T__4);
			setState(200);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class IfStmtContext extends ParserRuleContext {
		public ExprContext condition;
		public BlockStmtContext thenBlock;
		public BlockStmtContext elseBlock;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public List<BlockStmtContext> blockStmt() {
			return getRuleContexts(BlockStmtContext.class);
		}
		public BlockStmtContext blockStmt(int i) {
			return getRuleContext(BlockStmtContext.class,i);
		}
		public IfStmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ifStmt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterIfStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitIfStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitIfStmt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final IfStmtContext ifStmt() throws RecognitionException {
		IfStmtContext _localctx = new IfStmtContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_ifStmt);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(202);
			match(T__16);
			setState(203);
			match(T__2);
			setState(204);
			((IfStmtContext)_localctx).condition = expr();
			setState(205);
			match(T__4);
			setState(206);
			((IfStmtContext)_localctx).thenBlock = blockStmt();
			setState(209);
			_la = _input.LA(1);
			if (_la==T__17) {
				{
				setState(207);
				match(T__17);
				setState(208);
				((IfStmtContext)_localctx).elseBlock = blockStmt();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class WhileStmtContext extends ParserRuleContext {
		public ExprContext condition;
		public LoopInvariantContext loopInvariant;
		public List<LoopInvariantContext> invariantAnnotations = new ArrayList<LoopInvariantContext>();
		public BlockStmtContext body;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public BlockStmtContext blockStmt() {
			return getRuleContext(BlockStmtContext.class,0);
		}
		public List<LoopInvariantContext> loopInvariant() {
			return getRuleContexts(LoopInvariantContext.class);
		}
		public LoopInvariantContext loopInvariant(int i) {
			return getRuleContext(LoopInvariantContext.class,i);
		}
		public WhileStmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_whileStmt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterWhileStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitWhileStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitWhileStmt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final WhileStmtContext whileStmt() throws RecognitionException {
		WhileStmtContext _localctx = new WhileStmtContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_whileStmt);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(211);
			match(T__18);
			setState(212);
			match(T__2);
			setState(213);
			((WhileStmtContext)_localctx).condition = expr();
			setState(214);
			match(T__4);
			setState(223);
			_la = _input.LA(1);
			if (_la==T__19 || _la==T__20) {
				{
				setState(215);
				((WhileStmtContext)_localctx).loopInvariant = loopInvariant();
				((WhileStmtContext)_localctx).invariantAnnotations.add(((WhileStmtContext)_localctx).loopInvariant);
				setState(220);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__3) {
					{
					{
					setState(216);
					match(T__3);
					setState(217);
					((WhileStmtContext)_localctx).loopInvariant = loopInvariant();
					((WhileStmtContext)_localctx).invariantAnnotations.add(((WhileStmtContext)_localctx).loopInvariant);
					}
					}
					setState(222);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(225);
			((WhileStmtContext)_localctx).body = blockStmt();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BlockStmtContext extends ParserRuleContext {
		public StmtContext stmt;
		public List<StmtContext> stmts = new ArrayList<StmtContext>();
		public List<StmtContext> stmt() {
			return getRuleContexts(StmtContext.class);
		}
		public StmtContext stmt(int i) {
			return getRuleContext(StmtContext.class,i);
		}
		public BlockStmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_blockStmt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterBlockStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitBlockStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitBlockStmt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BlockStmtContext blockStmt() throws RecognitionException {
		BlockStmtContext _localctx = new BlockStmtContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_blockStmt);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(227);
			match(T__5);
			setState(231);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__0) | (1L << T__5) | (1L << T__13) | (1L << T__14) | (1L << T__15) | (1L << T__16) | (1L << T__18) | (1L << ID))) != 0)) {
				{
				{
				setState(228);
				((BlockStmtContext)_localctx).stmt = stmt();
				((BlockStmtContext)_localctx).stmts.add(((BlockStmtContext)_localctx).stmt);
				}
				}
				setState(233);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(234);
			match(T__7);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LoopInvariantContext extends ParserRuleContext {
		public InvariantContext invariant() {
			return getRuleContext(InvariantContext.class,0);
		}
		public CandidateInvariantContext candidateInvariant() {
			return getRuleContext(CandidateInvariantContext.class,0);
		}
		public LoopInvariantContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_loopInvariant; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterLoopInvariant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitLoopInvariant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitLoopInvariant(this);
			else return visitor.visitChildren(this);
		}
	}

	public final LoopInvariantContext loopInvariant() throws RecognitionException {
		LoopInvariantContext _localctx = new LoopInvariantContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_loopInvariant);
		try {
			setState(238);
			switch (_input.LA(1)) {
			case T__19:
				enterOuterAlt(_localctx, 1);
				{
				setState(236);
				invariant();
				}
				break;
			case T__20:
				enterOuterAlt(_localctx, 2);
				{
				setState(237);
				candidateInvariant();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class InvariantContext extends ParserRuleContext {
		public ExprContext condition;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public InvariantContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_invariant; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterInvariant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitInvariant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitInvariant(this);
			else return visitor.visitChildren(this);
		}
	}

	public final InvariantContext invariant() throws RecognitionException {
		InvariantContext _localctx = new InvariantContext(_ctx, getState());
		enterRule(_localctx, 38, RULE_invariant);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(240);
			match(T__19);
			setState(241);
			((InvariantContext)_localctx).condition = expr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class CandidateInvariantContext extends ParserRuleContext {
		public ExprContext condition;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public CandidateInvariantContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_candidateInvariant; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterCandidateInvariant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitCandidateInvariant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitCandidateInvariant(this);
			else return visitor.visitChildren(this);
		}
	}

	public final CandidateInvariantContext candidateInvariant() throws RecognitionException {
		CandidateInvariantContext _localctx = new CandidateInvariantContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_candidateInvariant);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(243);
			match(T__20);
			setState(244);
			((CandidateInvariantContext)_localctx).condition = expr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExprContext extends ParserRuleContext {
		public TernExprContext ternExpr() {
			return getRuleContext(TernExprContext.class,0);
		}
		public ExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExprContext expr() throws RecognitionException {
		ExprContext _localctx = new ExprContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_expr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(246);
			ternExpr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TernExprContext extends ParserRuleContext {
		public LorExprContext single;
		public LorExprContext lorExpr;
		public List<LorExprContext> args = new ArrayList<LorExprContext>();
		public List<LorExprContext> lorExpr() {
			return getRuleContexts(LorExprContext.class);
		}
		public LorExprContext lorExpr(int i) {
			return getRuleContext(LorExprContext.class,i);
		}
		public TernExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ternExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterTernExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitTernExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitTernExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TernExprContext ternExpr() throws RecognitionException {
		TernExprContext _localctx = new TernExprContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_ternExpr);
		int _la;
		try {
			setState(259);
			switch ( getInterpreter().adaptivePredict(_input,17,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(248);
				((TernExprContext)_localctx).single = lorExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(249);
				((TernExprContext)_localctx).lorExpr = lorExpr();
				((TernExprContext)_localctx).args.add(((TernExprContext)_localctx).lorExpr);
				setState(255); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(250);
					match(T__21);
					setState(251);
					((TernExprContext)_localctx).lorExpr = lorExpr();
					((TernExprContext)_localctx).args.add(((TernExprContext)_localctx).lorExpr);
					setState(252);
					match(T__22);
					setState(253);
					((TernExprContext)_localctx).lorExpr = lorExpr();
					((TernExprContext)_localctx).args.add(((TernExprContext)_localctx).lorExpr);
					}
					}
					setState(257); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__21 );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LorExprContext extends ParserRuleContext {
		public LandExprContext single;
		public LandExprContext landExpr;
		public List<LandExprContext> args = new ArrayList<LandExprContext>();
		public Token s24;
		public List<Token> ops = new ArrayList<Token>();
		public List<LandExprContext> landExpr() {
			return getRuleContexts(LandExprContext.class);
		}
		public LandExprContext landExpr(int i) {
			return getRuleContext(LandExprContext.class,i);
		}
		public LorExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_lorExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterLorExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitLorExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitLorExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final LorExprContext lorExpr() throws RecognitionException {
		LorExprContext _localctx = new LorExprContext(_ctx, getState());
		enterRule(_localctx, 46, RULE_lorExpr);
		int _la;
		try {
			setState(269);
			switch ( getInterpreter().adaptivePredict(_input,19,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(261);
				((LorExprContext)_localctx).single = landExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(262);
				((LorExprContext)_localctx).landExpr = landExpr();
				((LorExprContext)_localctx).args.add(((LorExprContext)_localctx).landExpr);
				setState(265); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(263);
					((LorExprContext)_localctx).s24 = match(T__23);
					((LorExprContext)_localctx).ops.add(((LorExprContext)_localctx).s24);
					setState(264);
					((LorExprContext)_localctx).landExpr = landExpr();
					((LorExprContext)_localctx).args.add(((LorExprContext)_localctx).landExpr);
					}
					}
					setState(267); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__23 );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LandExprContext extends ParserRuleContext {
		public BorExprContext single;
		public BorExprContext borExpr;
		public List<BorExprContext> args = new ArrayList<BorExprContext>();
		public Token s25;
		public List<Token> ops = new ArrayList<Token>();
		public List<BorExprContext> borExpr() {
			return getRuleContexts(BorExprContext.class);
		}
		public BorExprContext borExpr(int i) {
			return getRuleContext(BorExprContext.class,i);
		}
		public LandExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_landExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterLandExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitLandExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitLandExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final LandExprContext landExpr() throws RecognitionException {
		LandExprContext _localctx = new LandExprContext(_ctx, getState());
		enterRule(_localctx, 48, RULE_landExpr);
		int _la;
		try {
			setState(279);
			switch ( getInterpreter().adaptivePredict(_input,21,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(271);
				((LandExprContext)_localctx).single = borExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(272);
				((LandExprContext)_localctx).borExpr = borExpr();
				((LandExprContext)_localctx).args.add(((LandExprContext)_localctx).borExpr);
				setState(275); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(273);
					((LandExprContext)_localctx).s25 = match(T__24);
					((LandExprContext)_localctx).ops.add(((LandExprContext)_localctx).s25);
					setState(274);
					((LandExprContext)_localctx).borExpr = borExpr();
					((LandExprContext)_localctx).args.add(((LandExprContext)_localctx).borExpr);
					}
					}
					setState(277); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__24 );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BorExprContext extends ParserRuleContext {
		public BxorExprContext single;
		public BxorExprContext bxorExpr;
		public List<BxorExprContext> args = new ArrayList<BxorExprContext>();
		public Token s26;
		public List<Token> ops = new ArrayList<Token>();
		public List<BxorExprContext> bxorExpr() {
			return getRuleContexts(BxorExprContext.class);
		}
		public BxorExprContext bxorExpr(int i) {
			return getRuleContext(BxorExprContext.class,i);
		}
		public BorExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_borExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterBorExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitBorExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitBorExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BorExprContext borExpr() throws RecognitionException {
		BorExprContext _localctx = new BorExprContext(_ctx, getState());
		enterRule(_localctx, 50, RULE_borExpr);
		int _la;
		try {
			setState(289);
			switch ( getInterpreter().adaptivePredict(_input,23,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(281);
				((BorExprContext)_localctx).single = bxorExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(282);
				((BorExprContext)_localctx).bxorExpr = bxorExpr();
				((BorExprContext)_localctx).args.add(((BorExprContext)_localctx).bxorExpr);
				setState(285); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(283);
					((BorExprContext)_localctx).s26 = match(T__25);
					((BorExprContext)_localctx).ops.add(((BorExprContext)_localctx).s26);
					setState(284);
					((BorExprContext)_localctx).bxorExpr = bxorExpr();
					((BorExprContext)_localctx).args.add(((BorExprContext)_localctx).bxorExpr);
					}
					}
					setState(287); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__25 );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BxorExprContext extends ParserRuleContext {
		public BandExprContext single;
		public BandExprContext bandExpr;
		public List<BandExprContext> args = new ArrayList<BandExprContext>();
		public Token s27;
		public List<Token> ops = new ArrayList<Token>();
		public List<BandExprContext> bandExpr() {
			return getRuleContexts(BandExprContext.class);
		}
		public BandExprContext bandExpr(int i) {
			return getRuleContext(BandExprContext.class,i);
		}
		public BxorExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_bxorExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterBxorExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitBxorExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitBxorExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BxorExprContext bxorExpr() throws RecognitionException {
		BxorExprContext _localctx = new BxorExprContext(_ctx, getState());
		enterRule(_localctx, 52, RULE_bxorExpr);
		int _la;
		try {
			setState(299);
			switch ( getInterpreter().adaptivePredict(_input,25,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(291);
				((BxorExprContext)_localctx).single = bandExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(292);
				((BxorExprContext)_localctx).bandExpr = bandExpr();
				((BxorExprContext)_localctx).args.add(((BxorExprContext)_localctx).bandExpr);
				setState(295); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(293);
					((BxorExprContext)_localctx).s27 = match(T__26);
					((BxorExprContext)_localctx).ops.add(((BxorExprContext)_localctx).s27);
					setState(294);
					((BxorExprContext)_localctx).bandExpr = bandExpr();
					((BxorExprContext)_localctx).args.add(((BxorExprContext)_localctx).bandExpr);
					}
					}
					setState(297); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__26 );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BandExprContext extends ParserRuleContext {
		public EqualityExprContext single;
		public EqualityExprContext equalityExpr;
		public List<EqualityExprContext> args = new ArrayList<EqualityExprContext>();
		public Token s28;
		public List<Token> ops = new ArrayList<Token>();
		public List<EqualityExprContext> equalityExpr() {
			return getRuleContexts(EqualityExprContext.class);
		}
		public EqualityExprContext equalityExpr(int i) {
			return getRuleContext(EqualityExprContext.class,i);
		}
		public BandExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_bandExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterBandExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitBandExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitBandExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BandExprContext bandExpr() throws RecognitionException {
		BandExprContext _localctx = new BandExprContext(_ctx, getState());
		enterRule(_localctx, 54, RULE_bandExpr);
		int _la;
		try {
			setState(309);
			switch ( getInterpreter().adaptivePredict(_input,27,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(301);
				((BandExprContext)_localctx).single = equalityExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(302);
				((BandExprContext)_localctx).equalityExpr = equalityExpr();
				((BandExprContext)_localctx).args.add(((BandExprContext)_localctx).equalityExpr);
				setState(305); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(303);
					((BandExprContext)_localctx).s28 = match(T__27);
					((BandExprContext)_localctx).ops.add(((BandExprContext)_localctx).s28);
					setState(304);
					((BandExprContext)_localctx).equalityExpr = equalityExpr();
					((BandExprContext)_localctx).args.add(((BandExprContext)_localctx).equalityExpr);
					}
					}
					setState(307); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__27 );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EqualityExprContext extends ParserRuleContext {
		public RelExprContext single;
		public RelExprContext relExpr;
		public List<RelExprContext> args = new ArrayList<RelExprContext>();
		public Token s29;
		public List<Token> ops = new ArrayList<Token>();
		public Token s30;
		public List<RelExprContext> relExpr() {
			return getRuleContexts(RelExprContext.class);
		}
		public RelExprContext relExpr(int i) {
			return getRuleContext(RelExprContext.class,i);
		}
		public EqualityExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_equalityExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterEqualityExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitEqualityExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitEqualityExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final EqualityExprContext equalityExpr() throws RecognitionException {
		EqualityExprContext _localctx = new EqualityExprContext(_ctx, getState());
		enterRule(_localctx, 56, RULE_equalityExpr);
		int _la;
		try {
			setState(322);
			switch ( getInterpreter().adaptivePredict(_input,30,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(311);
				((EqualityExprContext)_localctx).single = relExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(312);
				((EqualityExprContext)_localctx).relExpr = relExpr();
				((EqualityExprContext)_localctx).args.add(((EqualityExprContext)_localctx).relExpr);
				setState(318); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(315);
					switch (_input.LA(1)) {
					case T__28:
						{
						setState(313);
						((EqualityExprContext)_localctx).s29 = match(T__28);
						((EqualityExprContext)_localctx).ops.add(((EqualityExprContext)_localctx).s29);
						}
						break;
					case T__29:
						{
						setState(314);
						((EqualityExprContext)_localctx).s30 = match(T__29);
						((EqualityExprContext)_localctx).ops.add(((EqualityExprContext)_localctx).s30);
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					setState(317);
					((EqualityExprContext)_localctx).relExpr = relExpr();
					((EqualityExprContext)_localctx).args.add(((EqualityExprContext)_localctx).relExpr);
					}
					}
					setState(320); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__28 || _la==T__29 );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class RelExprContext extends ParserRuleContext {
		public ShiftExprContext single;
		public ShiftExprContext shiftExpr;
		public List<ShiftExprContext> args = new ArrayList<ShiftExprContext>();
		public Token s31;
		public List<Token> ops = new ArrayList<Token>();
		public Token s32;
		public Token s33;
		public Token s34;
		public List<ShiftExprContext> shiftExpr() {
			return getRuleContexts(ShiftExprContext.class);
		}
		public ShiftExprContext shiftExpr(int i) {
			return getRuleContext(ShiftExprContext.class,i);
		}
		public RelExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_relExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterRelExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitRelExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitRelExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final RelExprContext relExpr() throws RecognitionException {
		RelExprContext _localctx = new RelExprContext(_ctx, getState());
		enterRule(_localctx, 58, RULE_relExpr);
		int _la;
		try {
			setState(337);
			switch ( getInterpreter().adaptivePredict(_input,33,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(324);
				((RelExprContext)_localctx).single = shiftExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(325);
				((RelExprContext)_localctx).shiftExpr = shiftExpr();
				((RelExprContext)_localctx).args.add(((RelExprContext)_localctx).shiftExpr);
				setState(333); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(330);
					switch (_input.LA(1)) {
					case T__30:
						{
						setState(326);
						((RelExprContext)_localctx).s31 = match(T__30);
						((RelExprContext)_localctx).ops.add(((RelExprContext)_localctx).s31);
						}
						break;
					case T__31:
						{
						setState(327);
						((RelExprContext)_localctx).s32 = match(T__31);
						((RelExprContext)_localctx).ops.add(((RelExprContext)_localctx).s32);
						}
						break;
					case T__32:
						{
						setState(328);
						((RelExprContext)_localctx).s33 = match(T__32);
						((RelExprContext)_localctx).ops.add(((RelExprContext)_localctx).s33);
						}
						break;
					case T__33:
						{
						setState(329);
						((RelExprContext)_localctx).s34 = match(T__33);
						((RelExprContext)_localctx).ops.add(((RelExprContext)_localctx).s34);
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					setState(332);
					((RelExprContext)_localctx).shiftExpr = shiftExpr();
					((RelExprContext)_localctx).args.add(((RelExprContext)_localctx).shiftExpr);
					}
					}
					setState(335); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__30) | (1L << T__31) | (1L << T__32) | (1L << T__33))) != 0) );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ShiftExprContext extends ParserRuleContext {
		public AddExprContext single;
		public AddExprContext addExpr;
		public List<AddExprContext> args = new ArrayList<AddExprContext>();
		public Token s35;
		public List<Token> ops = new ArrayList<Token>();
		public Token s36;
		public List<AddExprContext> addExpr() {
			return getRuleContexts(AddExprContext.class);
		}
		public AddExprContext addExpr(int i) {
			return getRuleContext(AddExprContext.class,i);
		}
		public ShiftExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_shiftExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterShiftExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitShiftExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitShiftExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ShiftExprContext shiftExpr() throws RecognitionException {
		ShiftExprContext _localctx = new ShiftExprContext(_ctx, getState());
		enterRule(_localctx, 60, RULE_shiftExpr);
		int _la;
		try {
			setState(350);
			switch ( getInterpreter().adaptivePredict(_input,36,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(339);
				((ShiftExprContext)_localctx).single = addExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(340);
				((ShiftExprContext)_localctx).addExpr = addExpr();
				((ShiftExprContext)_localctx).args.add(((ShiftExprContext)_localctx).addExpr);
				setState(346); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(343);
					switch (_input.LA(1)) {
					case T__34:
						{
						setState(341);
						((ShiftExprContext)_localctx).s35 = match(T__34);
						((ShiftExprContext)_localctx).ops.add(((ShiftExprContext)_localctx).s35);
						}
						break;
					case T__35:
						{
						setState(342);
						((ShiftExprContext)_localctx).s36 = match(T__35);
						((ShiftExprContext)_localctx).ops.add(((ShiftExprContext)_localctx).s36);
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					setState(345);
					((ShiftExprContext)_localctx).addExpr = addExpr();
					((ShiftExprContext)_localctx).args.add(((ShiftExprContext)_localctx).addExpr);
					}
					}
					setState(348); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__34 || _la==T__35 );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AddExprContext extends ParserRuleContext {
		public MulExprContext single;
		public MulExprContext mulExpr;
		public List<MulExprContext> args = new ArrayList<MulExprContext>();
		public Token s37;
		public List<Token> ops = new ArrayList<Token>();
		public Token s38;
		public List<MulExprContext> mulExpr() {
			return getRuleContexts(MulExprContext.class);
		}
		public MulExprContext mulExpr(int i) {
			return getRuleContext(MulExprContext.class,i);
		}
		public AddExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_addExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterAddExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitAddExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitAddExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AddExprContext addExpr() throws RecognitionException {
		AddExprContext _localctx = new AddExprContext(_ctx, getState());
		enterRule(_localctx, 62, RULE_addExpr);
		int _la;
		try {
			setState(363);
			switch ( getInterpreter().adaptivePredict(_input,39,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(352);
				((AddExprContext)_localctx).single = mulExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(353);
				((AddExprContext)_localctx).mulExpr = mulExpr();
				((AddExprContext)_localctx).args.add(((AddExprContext)_localctx).mulExpr);
				setState(359); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(356);
					switch (_input.LA(1)) {
					case T__36:
						{
						setState(354);
						((AddExprContext)_localctx).s37 = match(T__36);
						((AddExprContext)_localctx).ops.add(((AddExprContext)_localctx).s37);
						}
						break;
					case T__37:
						{
						setState(355);
						((AddExprContext)_localctx).s38 = match(T__37);
						((AddExprContext)_localctx).ops.add(((AddExprContext)_localctx).s38);
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					setState(358);
					((AddExprContext)_localctx).mulExpr = mulExpr();
					((AddExprContext)_localctx).args.add(((AddExprContext)_localctx).mulExpr);
					}
					}
					setState(361); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__36 || _la==T__37 );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MulExprContext extends ParserRuleContext {
		public UnaryExprContext single;
		public UnaryExprContext unaryExpr;
		public List<UnaryExprContext> args = new ArrayList<UnaryExprContext>();
		public Token s39;
		public List<Token> ops = new ArrayList<Token>();
		public Token s40;
		public Token s41;
		public List<UnaryExprContext> unaryExpr() {
			return getRuleContexts(UnaryExprContext.class);
		}
		public UnaryExprContext unaryExpr(int i) {
			return getRuleContext(UnaryExprContext.class,i);
		}
		public MulExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_mulExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterMulExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitMulExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitMulExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final MulExprContext mulExpr() throws RecognitionException {
		MulExprContext _localctx = new MulExprContext(_ctx, getState());
		enterRule(_localctx, 64, RULE_mulExpr);
		int _la;
		try {
			setState(377);
			switch ( getInterpreter().adaptivePredict(_input,42,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(365);
				((MulExprContext)_localctx).single = unaryExpr();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(366);
				((MulExprContext)_localctx).unaryExpr = unaryExpr();
				((MulExprContext)_localctx).args.add(((MulExprContext)_localctx).unaryExpr);
				setState(373); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(370);
					switch (_input.LA(1)) {
					case T__38:
						{
						setState(367);
						((MulExprContext)_localctx).s39 = match(T__38);
						((MulExprContext)_localctx).ops.add(((MulExprContext)_localctx).s39);
						}
						break;
					case T__39:
						{
						setState(368);
						((MulExprContext)_localctx).s40 = match(T__39);
						((MulExprContext)_localctx).ops.add(((MulExprContext)_localctx).s40);
						}
						break;
					case T__40:
						{
						setState(369);
						((MulExprContext)_localctx).s41 = match(T__40);
						((MulExprContext)_localctx).ops.add(((MulExprContext)_localctx).s41);
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					setState(372);
					((MulExprContext)_localctx).unaryExpr = unaryExpr();
					((MulExprContext)_localctx).args.add(((MulExprContext)_localctx).unaryExpr);
					}
					}
					setState(375); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__38) | (1L << T__39) | (1L << T__40))) != 0) );
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class UnaryExprContext extends ParserRuleContext {
		public AtomExprContext single;
		public Token s37;
		public List<Token> ops = new ArrayList<Token>();
		public Token s38;
		public Token s42;
		public Token s43;
		public AtomExprContext arg;
		public AtomExprContext atomExpr() {
			return getRuleContext(AtomExprContext.class,0);
		}
		public UnaryExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_unaryExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterUnaryExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitUnaryExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitUnaryExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UnaryExprContext unaryExpr() throws RecognitionException {
		UnaryExprContext _localctx = new UnaryExprContext(_ctx, getState());
		enterRule(_localctx, 66, RULE_unaryExpr);
		int _la;
		try {
			setState(389);
			switch (_input.LA(1)) {
			case T__2:
			case T__43:
			case T__44:
			case ID:
			case NUMBER:
				enterOuterAlt(_localctx, 1);
				{
				setState(379);
				((UnaryExprContext)_localctx).single = atomExpr();
				}
				break;
			case T__36:
			case T__37:
			case T__41:
			case T__42:
				enterOuterAlt(_localctx, 2);
				{
				setState(384); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					setState(384);
					switch (_input.LA(1)) {
					case T__36:
						{
						setState(380);
						((UnaryExprContext)_localctx).s37 = match(T__36);
						((UnaryExprContext)_localctx).ops.add(((UnaryExprContext)_localctx).s37);
						}
						break;
					case T__37:
						{
						setState(381);
						((UnaryExprContext)_localctx).s38 = match(T__37);
						((UnaryExprContext)_localctx).ops.add(((UnaryExprContext)_localctx).s38);
						}
						break;
					case T__41:
						{
						setState(382);
						((UnaryExprContext)_localctx).s42 = match(T__41);
						((UnaryExprContext)_localctx).ops.add(((UnaryExprContext)_localctx).s42);
						}
						break;
					case T__42:
						{
						setState(383);
						((UnaryExprContext)_localctx).s43 = match(T__42);
						((UnaryExprContext)_localctx).ops.add(((UnaryExprContext)_localctx).s43);
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					}
					setState(386); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__36) | (1L << T__37) | (1L << T__41) | (1L << T__42))) != 0) );
				setState(388);
				((UnaryExprContext)_localctx).arg = atomExpr();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AtomExprContext extends ParserRuleContext {
		public NumberExprContext numberExpr() {
			return getRuleContext(NumberExprContext.class,0);
		}
		public VarrefExprContext varrefExpr() {
			return getRuleContext(VarrefExprContext.class,0);
		}
		public ParenExprContext parenExpr() {
			return getRuleContext(ParenExprContext.class,0);
		}
		public ResultExprContext resultExpr() {
			return getRuleContext(ResultExprContext.class,0);
		}
		public OldExprContext oldExpr() {
			return getRuleContext(OldExprContext.class,0);
		}
		public AtomExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_atomExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterAtomExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitAtomExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitAtomExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AtomExprContext atomExpr() throws RecognitionException {
		AtomExprContext _localctx = new AtomExprContext(_ctx, getState());
		enterRule(_localctx, 68, RULE_atomExpr);
		try {
			setState(396);
			switch (_input.LA(1)) {
			case NUMBER:
				enterOuterAlt(_localctx, 1);
				{
				setState(391);
				numberExpr();
				}
				break;
			case ID:
				enterOuterAlt(_localctx, 2);
				{
				setState(392);
				varrefExpr();
				}
				break;
			case T__2:
				enterOuterAlt(_localctx, 3);
				{
				setState(393);
				parenExpr();
				}
				break;
			case T__43:
				enterOuterAlt(_localctx, 4);
				{
				setState(394);
				resultExpr();
				}
				break;
			case T__44:
				enterOuterAlt(_localctx, 5);
				{
				setState(395);
				oldExpr();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class NumberExprContext extends ParserRuleContext {
		public Token number;
		public TerminalNode NUMBER() { return getToken(SimpleCParser.NUMBER, 0); }
		public NumberExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_numberExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterNumberExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitNumberExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitNumberExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final NumberExprContext numberExpr() throws RecognitionException {
		NumberExprContext _localctx = new NumberExprContext(_ctx, getState());
		enterRule(_localctx, 70, RULE_numberExpr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(398);
			((NumberExprContext)_localctx).number = match(NUMBER);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VarrefExprContext extends ParserRuleContext {
		public VarrefContext var;
		public VarrefContext varref() {
			return getRuleContext(VarrefContext.class,0);
		}
		public VarrefExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varrefExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterVarrefExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitVarrefExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitVarrefExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarrefExprContext varrefExpr() throws RecognitionException {
		VarrefExprContext _localctx = new VarrefExprContext(_ctx, getState());
		enterRule(_localctx, 72, RULE_varrefExpr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(400);
			((VarrefExprContext)_localctx).var = varref();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ParenExprContext extends ParserRuleContext {
		public ExprContext arg;
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public ParenExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_parenExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterParenExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitParenExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitParenExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ParenExprContext parenExpr() throws RecognitionException {
		ParenExprContext _localctx = new ParenExprContext(_ctx, getState());
		enterRule(_localctx, 74, RULE_parenExpr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(402);
			match(T__2);
			setState(403);
			((ParenExprContext)_localctx).arg = expr();
			setState(404);
			match(T__4);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ResultExprContext extends ParserRuleContext {
		public Token resultTok;
		public ResultExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_resultExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterResultExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitResultExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitResultExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ResultExprContext resultExpr() throws RecognitionException {
		ResultExprContext _localctx = new ResultExprContext(_ctx, getState());
		enterRule(_localctx, 76, RULE_resultExpr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(406);
			((ResultExprContext)_localctx).resultTok = match(T__43);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class OldExprContext extends ParserRuleContext {
		public Token oldTok;
		public VarrefContext arg;
		public VarrefContext varref() {
			return getRuleContext(VarrefContext.class,0);
		}
		public OldExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_oldExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterOldExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitOldExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitOldExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final OldExprContext oldExpr() throws RecognitionException {
		OldExprContext _localctx = new OldExprContext(_ctx, getState());
		enterRule(_localctx, 78, RULE_oldExpr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(408);
			((OldExprContext)_localctx).oldTok = match(T__44);
			setState(409);
			match(T__2);
			setState(410);
			((OldExprContext)_localctx).arg = varref();
			setState(411);
			match(T__4);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VarrefContext extends ParserRuleContext {
		public VarIdentifierContext ident;
		public VarIdentifierContext varIdentifier() {
			return getRuleContext(VarIdentifierContext.class,0);
		}
		public VarrefContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varref; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterVarref(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitVarref(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitVarref(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarrefContext varref() throws RecognitionException {
		VarrefContext _localctx = new VarrefContext(_ctx, getState());
		enterRule(_localctx, 80, RULE_varref);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(413);
			((VarrefContext)_localctx).ident = varIdentifier();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VarIdentifierContext extends ParserRuleContext {
		public Token name;
		public TerminalNode ID() { return getToken(SimpleCParser.ID, 0); }
		public VarIdentifierContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varIdentifier; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).enterVarIdentifier(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleCListener ) ((SimpleCListener)listener).exitVarIdentifier(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SimpleCVisitor ) return ((SimpleCVisitor<? extends T>)visitor).visitVarIdentifier(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarIdentifierContext varIdentifier() throws RecognitionException {
		VarIdentifierContext _localctx = new VarIdentifierContext(_ctx, getState());
		enterRule(_localctx, 82, RULE_varIdentifier);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(415);
			((VarIdentifierContext)_localctx).name = match(ID);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\3\65\u01a4\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\3"+
		"\2\7\2X\n\2\f\2\16\2[\13\2\3\2\7\2^\n\2\f\2\16\2a\13\2\3\3\3\3\3\3\3\3"+
		"\3\4\3\4\3\4\3\4\3\4\3\4\7\4m\n\4\f\4\16\4p\13\4\5\4r\n\4\3\4\3\4\3\4"+
		"\3\4\7\4x\n\4\f\4\16\4{\13\4\5\4}\n\4\3\4\3\4\7\4\u0081\n\4\f\4\16\4\u0084"+
		"\13\4\3\4\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3\6\3\6\3\6\3\6\5\6\u0092\n\6\3"+
		"\7\3\7\3\7\3\b\3\b\3\b\3\t\3\t\3\t\3\n\3\n\3\n\3\13\3\13\3\13\3\13\3\13"+
		"\3\13\3\13\3\13\3\13\5\13\u00a9\n\13\3\f\3\f\3\f\3\f\3\f\3\r\3\r\3\r\3"+
		"\r\3\16\3\16\3\16\3\16\3\17\3\17\3\17\3\17\3\20\3\20\3\20\3\20\3\20\3"+
		"\20\3\20\7\20\u00c3\n\20\f\20\16\20\u00c6\13\20\5\20\u00c8\n\20\3\20\3"+
		"\20\3\20\3\21\3\21\3\21\3\21\3\21\3\21\3\21\5\21\u00d4\n\21\3\22\3\22"+
		"\3\22\3\22\3\22\3\22\3\22\7\22\u00dd\n\22\f\22\16\22\u00e0\13\22\5\22"+
		"\u00e2\n\22\3\22\3\22\3\23\3\23\7\23\u00e8\n\23\f\23\16\23\u00eb\13\23"+
		"\3\23\3\23\3\24\3\24\5\24\u00f1\n\24\3\25\3\25\3\25\3\26\3\26\3\26\3\27"+
		"\3\27\3\30\3\30\3\30\3\30\3\30\3\30\3\30\6\30\u0102\n\30\r\30\16\30\u0103"+
		"\5\30\u0106\n\30\3\31\3\31\3\31\3\31\6\31\u010c\n\31\r\31\16\31\u010d"+
		"\5\31\u0110\n\31\3\32\3\32\3\32\3\32\6\32\u0116\n\32\r\32\16\32\u0117"+
		"\5\32\u011a\n\32\3\33\3\33\3\33\3\33\6\33\u0120\n\33\r\33\16\33\u0121"+
		"\5\33\u0124\n\33\3\34\3\34\3\34\3\34\6\34\u012a\n\34\r\34\16\34\u012b"+
		"\5\34\u012e\n\34\3\35\3\35\3\35\3\35\6\35\u0134\n\35\r\35\16\35\u0135"+
		"\5\35\u0138\n\35\3\36\3\36\3\36\3\36\5\36\u013e\n\36\3\36\6\36\u0141\n"+
		"\36\r\36\16\36\u0142\5\36\u0145\n\36\3\37\3\37\3\37\3\37\3\37\3\37\5\37"+
		"\u014d\n\37\3\37\6\37\u0150\n\37\r\37\16\37\u0151\5\37\u0154\n\37\3 \3"+
		" \3 \3 \5 \u015a\n \3 \6 \u015d\n \r \16 \u015e\5 \u0161\n \3!\3!\3!\3"+
		"!\5!\u0167\n!\3!\6!\u016a\n!\r!\16!\u016b\5!\u016e\n!\3\"\3\"\3\"\3\""+
		"\3\"\5\"\u0175\n\"\3\"\6\"\u0178\n\"\r\"\16\"\u0179\5\"\u017c\n\"\3#\3"+
		"#\3#\3#\3#\6#\u0183\n#\r#\16#\u0184\3#\5#\u0188\n#\3$\3$\3$\3$\3$\5$\u018f"+
		"\n$\3%\3%\3&\3&\3\'\3\'\3\'\3\'\3(\3(\3)\3)\3)\3)\3)\3*\3*\3+\3+\3+\2"+
		"\2,\2\4\6\b\n\f\16\20\22\24\26\30\32\34\36 \"$&(*,.\60\62\64\668:<>@B"+
		"DFHJLNPRT\2\2\u01b9\2Y\3\2\2\2\4b\3\2\2\2\6f\3\2\2\2\b\u008a\3\2\2\2\n"+
		"\u0091\3\2\2\2\f\u0093\3\2\2\2\16\u0096\3\2\2\2\20\u0099\3\2\2\2\22\u009c"+
		"\3\2\2\2\24\u00a8\3\2\2\2\26\u00aa\3\2\2\2\30\u00af\3\2\2\2\32\u00b3\3"+
		"\2\2\2\34\u00b7\3\2\2\2\36\u00bb\3\2\2\2 \u00cc\3\2\2\2\"\u00d5\3\2\2"+
		"\2$\u00e5\3\2\2\2&\u00f0\3\2\2\2(\u00f2\3\2\2\2*\u00f5\3\2\2\2,\u00f8"+
		"\3\2\2\2.\u0105\3\2\2\2\60\u010f\3\2\2\2\62\u0119\3\2\2\2\64\u0123\3\2"+
		"\2\2\66\u012d\3\2\2\28\u0137\3\2\2\2:\u0144\3\2\2\2<\u0153\3\2\2\2>\u0160"+
		"\3\2\2\2@\u016d\3\2\2\2B\u017b\3\2\2\2D\u0187\3\2\2\2F\u018e\3\2\2\2H"+
		"\u0190\3\2\2\2J\u0192\3\2\2\2L\u0194\3\2\2\2N\u0198\3\2\2\2P\u019a\3\2"+
		"\2\2R\u019f\3\2\2\2T\u01a1\3\2\2\2VX\5\4\3\2WV\3\2\2\2X[\3\2\2\2YW\3\2"+
		"\2\2YZ\3\2\2\2Z_\3\2\2\2[Y\3\2\2\2\\^\5\6\4\2]\\\3\2\2\2^a\3\2\2\2_]\3"+
		"\2\2\2_`\3\2\2\2`\3\3\2\2\2a_\3\2\2\2bc\7\3\2\2cd\5T+\2de\7\4\2\2e\5\3"+
		"\2\2\2fg\7\3\2\2gh\7\60\2\2hq\7\5\2\2in\5\b\5\2jk\7\6\2\2km\5\b\5\2lj"+
		"\3\2\2\2mp\3\2\2\2nl\3\2\2\2no\3\2\2\2or\3\2\2\2pn\3\2\2\2qi\3\2\2\2q"+
		"r\3\2\2\2rs\3\2\2\2s|\7\7\2\2ty\5\n\6\2uv\7\6\2\2vx\5\n\6\2wu\3\2\2\2"+
		"x{\3\2\2\2yw\3\2\2\2yz\3\2\2\2z}\3\2\2\2{y\3\2\2\2|t\3\2\2\2|}\3\2\2\2"+
		"}~\3\2\2\2~\u0082\7\b\2\2\177\u0081\5\24\13\2\u0080\177\3\2\2\2\u0081"+
		"\u0084\3\2\2\2\u0082\u0080\3\2\2\2\u0082\u0083\3\2\2\2\u0083\u0085\3\2"+
		"\2\2\u0084\u0082\3\2\2\2\u0085\u0086\7\t\2\2\u0086\u0087\5,\27\2\u0087"+
		"\u0088\7\4\2\2\u0088\u0089\7\n\2\2\u0089\7\3\2\2\2\u008a\u008b\7\3\2\2"+
		"\u008b\u008c\5T+\2\u008c\t\3\2\2\2\u008d\u0092\5\f\7\2\u008e\u0092\5\16"+
		"\b\2\u008f\u0092\5\20\t\2\u0090\u0092\5\22\n\2\u0091\u008d\3\2\2\2\u0091"+
		"\u008e\3\2\2\2\u0091\u008f\3\2\2\2\u0091\u0090\3\2\2\2\u0092\13\3\2\2"+
		"\2\u0093\u0094\7\13\2\2\u0094\u0095\5,\27\2\u0095\r\3\2\2\2\u0096\u0097"+
		"\7\f\2\2\u0097\u0098\5,\27\2\u0098\17\3\2\2\2\u0099\u009a\7\r\2\2\u009a"+
		"\u009b\5,\27\2\u009b\21\3\2\2\2\u009c\u009d\7\16\2\2\u009d\u009e\5,\27"+
		"\2\u009e\23\3\2\2\2\u009f\u00a9\5\4\3\2\u00a0\u00a9\5\26\f\2\u00a1\u00a9"+
		"\5\30\r\2\u00a2\u00a9\5\32\16\2\u00a3\u00a9\5\34\17\2\u00a4\u00a9\5\36"+
		"\20\2\u00a5\u00a9\5 \21\2\u00a6\u00a9\5\"\22\2\u00a7\u00a9\5$\23\2\u00a8"+
		"\u009f\3\2\2\2\u00a8\u00a0\3\2\2\2\u00a8\u00a1\3\2\2\2\u00a8\u00a2\3\2"+
		"\2\2\u00a8\u00a3\3\2\2\2\u00a8\u00a4\3\2\2\2\u00a8\u00a5\3\2\2\2\u00a8"+
		"\u00a6\3\2\2\2\u00a8\u00a7\3\2\2\2\u00a9\25\3\2\2\2\u00aa\u00ab\5R*\2"+
		"\u00ab\u00ac\7\17\2\2\u00ac\u00ad\5,\27\2\u00ad\u00ae\7\4\2\2\u00ae\27"+
		"\3\2\2\2\u00af\u00b0\7\20\2\2\u00b0\u00b1\5,\27\2\u00b1\u00b2\7\4\2\2"+
		"\u00b2\31\3\2\2\2\u00b3\u00b4\7\21\2\2\u00b4\u00b5\5,\27\2\u00b5\u00b6"+
		"\7\4\2\2\u00b6\33\3\2\2\2\u00b7\u00b8\7\22\2\2\u00b8\u00b9\5R*\2\u00b9"+
		"\u00ba\7\4\2\2\u00ba\35\3\2\2\2\u00bb\u00bc\5R*\2\u00bc\u00bd\7\17\2\2"+
		"\u00bd\u00be\7\60\2\2\u00be\u00c7\7\5\2\2\u00bf\u00c4\5,\27\2\u00c0\u00c1"+
		"\7\6\2\2\u00c1\u00c3\5,\27\2\u00c2\u00c0\3\2\2\2\u00c3\u00c6\3\2\2\2\u00c4"+
		"\u00c2\3\2\2\2\u00c4\u00c5\3\2\2\2\u00c5\u00c8\3\2\2\2\u00c6\u00c4\3\2"+
		"\2\2\u00c7\u00bf\3\2\2\2\u00c7\u00c8\3\2\2\2\u00c8\u00c9\3\2\2\2\u00c9"+
		"\u00ca\7\7\2\2\u00ca\u00cb\7\4\2\2\u00cb\37\3\2\2\2\u00cc\u00cd\7\23\2"+
		"\2\u00cd\u00ce\7\5\2\2\u00ce\u00cf\5,\27\2\u00cf\u00d0\7\7\2\2\u00d0\u00d3"+
		"\5$\23\2\u00d1\u00d2\7\24\2\2\u00d2\u00d4\5$\23\2\u00d3\u00d1\3\2\2\2"+
		"\u00d3\u00d4\3\2\2\2\u00d4!\3\2\2\2\u00d5\u00d6\7\25\2\2\u00d6\u00d7\7"+
		"\5\2\2\u00d7\u00d8\5,\27\2\u00d8\u00e1\7\7\2\2\u00d9\u00de\5&\24\2\u00da"+
		"\u00db\7\6\2\2\u00db\u00dd\5&\24\2\u00dc\u00da\3\2\2\2\u00dd\u00e0\3\2"+
		"\2\2\u00de\u00dc\3\2\2\2\u00de\u00df\3\2\2\2\u00df\u00e2\3\2\2\2\u00e0"+
		"\u00de\3\2\2\2\u00e1\u00d9\3\2\2\2\u00e1\u00e2\3\2\2\2\u00e2\u00e3\3\2"+
		"\2\2\u00e3\u00e4\5$\23\2\u00e4#\3\2\2\2\u00e5\u00e9\7\b\2\2\u00e6\u00e8"+
		"\5\24\13\2\u00e7\u00e6\3\2\2\2\u00e8\u00eb\3\2\2\2\u00e9\u00e7\3\2\2\2"+
		"\u00e9\u00ea\3\2\2\2\u00ea\u00ec\3\2\2\2\u00eb\u00e9\3\2\2\2\u00ec\u00ed"+
		"\7\n\2\2\u00ed%\3\2\2\2\u00ee\u00f1\5(\25\2\u00ef\u00f1\5*\26\2\u00f0"+
		"\u00ee\3\2\2\2\u00f0\u00ef\3\2\2\2\u00f1\'\3\2\2\2\u00f2\u00f3\7\26\2"+
		"\2\u00f3\u00f4\5,\27\2\u00f4)\3\2\2\2\u00f5\u00f6\7\27\2\2\u00f6\u00f7"+
		"\5,\27\2\u00f7+\3\2\2\2\u00f8\u00f9\5.\30\2\u00f9-\3\2\2\2\u00fa\u0106"+
		"\5\60\31\2\u00fb\u0101\5\60\31\2\u00fc\u00fd\7\30\2\2\u00fd\u00fe\5\60"+
		"\31\2\u00fe\u00ff\7\31\2\2\u00ff\u0100\5\60\31\2\u0100\u0102\3\2\2\2\u0101"+
		"\u00fc\3\2\2\2\u0102\u0103\3\2\2\2\u0103\u0101\3\2\2\2\u0103\u0104\3\2"+
		"\2\2\u0104\u0106\3\2\2\2\u0105\u00fa\3\2\2\2\u0105\u00fb\3\2\2\2\u0106"+
		"/\3\2\2\2\u0107\u0110\5\62\32\2\u0108\u010b\5\62\32\2\u0109\u010a\7\32"+
		"\2\2\u010a\u010c\5\62\32\2\u010b\u0109\3\2\2\2\u010c\u010d\3\2\2\2\u010d"+
		"\u010b\3\2\2\2\u010d\u010e\3\2\2\2\u010e\u0110\3\2\2\2\u010f\u0107\3\2"+
		"\2\2\u010f\u0108\3\2\2\2\u0110\61\3\2\2\2\u0111\u011a\5\64\33\2\u0112"+
		"\u0115\5\64\33\2\u0113\u0114\7\33\2\2\u0114\u0116\5\64\33\2\u0115\u0113"+
		"\3\2\2\2\u0116\u0117\3\2\2\2\u0117\u0115\3\2\2\2\u0117\u0118\3\2\2\2\u0118"+
		"\u011a\3\2\2\2\u0119\u0111\3\2\2\2\u0119\u0112\3\2\2\2\u011a\63\3\2\2"+
		"\2\u011b\u0124\5\66\34\2\u011c\u011f\5\66\34\2\u011d\u011e\7\34\2\2\u011e"+
		"\u0120\5\66\34\2\u011f\u011d\3\2\2\2\u0120\u0121\3\2\2\2\u0121\u011f\3"+
		"\2\2\2\u0121\u0122\3\2\2\2\u0122\u0124\3\2\2\2\u0123\u011b\3\2\2\2\u0123"+
		"\u011c\3\2\2\2\u0124\65\3\2\2\2\u0125\u012e\58\35\2\u0126\u0129\58\35"+
		"\2\u0127\u0128\7\35\2\2\u0128\u012a\58\35\2\u0129\u0127\3\2\2\2\u012a"+
		"\u012b\3\2\2\2\u012b\u0129\3\2\2\2\u012b\u012c\3\2\2\2\u012c\u012e\3\2"+
		"\2\2\u012d\u0125\3\2\2\2\u012d\u0126\3\2\2\2\u012e\67\3\2\2\2\u012f\u0138"+
		"\5:\36\2\u0130\u0133\5:\36\2\u0131\u0132\7\36\2\2\u0132\u0134\5:\36\2"+
		"\u0133\u0131\3\2\2\2\u0134\u0135\3\2\2\2\u0135\u0133\3\2\2\2\u0135\u0136"+
		"\3\2\2\2\u0136\u0138\3\2\2\2\u0137\u012f\3\2\2\2\u0137\u0130\3\2\2\2\u0138"+
		"9\3\2\2\2\u0139\u0145\5<\37\2\u013a\u0140\5<\37\2\u013b\u013e\7\37\2\2"+
		"\u013c\u013e\7 \2\2\u013d\u013b\3\2\2\2\u013d\u013c\3\2\2\2\u013e\u013f"+
		"\3\2\2\2\u013f\u0141\5<\37\2\u0140\u013d\3\2\2\2\u0141\u0142\3\2\2\2\u0142"+
		"\u0140\3\2\2\2\u0142\u0143\3\2\2\2\u0143\u0145\3\2\2\2\u0144\u0139\3\2"+
		"\2\2\u0144\u013a\3\2\2\2\u0145;\3\2\2\2\u0146\u0154\5> \2\u0147\u014f"+
		"\5> \2\u0148\u014d\7!\2\2\u0149\u014d\7\"\2\2\u014a\u014d\7#\2\2\u014b"+
		"\u014d\7$\2\2\u014c\u0148\3\2\2\2\u014c\u0149\3\2\2\2\u014c\u014a\3\2"+
		"\2\2\u014c\u014b\3\2\2\2\u014d\u014e\3\2\2\2\u014e\u0150\5> \2\u014f\u014c"+
		"\3\2\2\2\u0150\u0151\3\2\2\2\u0151\u014f\3\2\2\2\u0151\u0152\3\2\2\2\u0152"+
		"\u0154\3\2\2\2\u0153\u0146\3\2\2\2\u0153\u0147\3\2\2\2\u0154=\3\2\2\2"+
		"\u0155\u0161\5@!\2\u0156\u015c\5@!\2\u0157\u015a\7%\2\2\u0158\u015a\7"+
		"&\2\2\u0159\u0157\3\2\2\2\u0159\u0158\3\2\2\2\u015a\u015b\3\2\2\2\u015b"+
		"\u015d\5@!\2\u015c\u0159\3\2\2\2\u015d\u015e\3\2\2\2\u015e\u015c\3\2\2"+
		"\2\u015e\u015f\3\2\2\2\u015f\u0161\3\2\2\2\u0160\u0155\3\2\2\2\u0160\u0156"+
		"\3\2\2\2\u0161?\3\2\2\2\u0162\u016e\5B\"\2\u0163\u0169\5B\"\2\u0164\u0167"+
		"\7\'\2\2\u0165\u0167\7(\2\2\u0166\u0164\3\2\2\2\u0166\u0165\3\2\2\2\u0167"+
		"\u0168\3\2\2\2\u0168\u016a\5B\"\2\u0169\u0166\3\2\2\2\u016a\u016b\3\2"+
		"\2\2\u016b\u0169\3\2\2\2\u016b\u016c\3\2\2\2\u016c\u016e\3\2\2\2\u016d"+
		"\u0162\3\2\2\2\u016d\u0163\3\2\2\2\u016eA\3\2\2\2\u016f\u017c\5D#\2\u0170"+
		"\u0177\5D#\2\u0171\u0175\7)\2\2\u0172\u0175\7*\2\2\u0173\u0175\7+\2\2"+
		"\u0174\u0171\3\2\2\2\u0174\u0172\3\2\2\2\u0174\u0173\3\2\2\2\u0175\u0176"+
		"\3\2\2\2\u0176\u0178\5D#\2\u0177\u0174\3\2\2\2\u0178\u0179\3\2\2\2\u0179"+
		"\u0177\3\2\2\2\u0179\u017a\3\2\2\2\u017a\u017c\3\2\2\2\u017b\u016f\3\2"+
		"\2\2\u017b\u0170\3\2\2\2\u017cC\3\2\2\2\u017d\u0188\5F$\2\u017e\u0183"+
		"\7\'\2\2\u017f\u0183\7(\2\2\u0180\u0183\7,\2\2\u0181\u0183\7-\2\2\u0182"+
		"\u017e\3\2\2\2\u0182\u017f\3\2\2\2\u0182\u0180\3\2\2\2\u0182\u0181\3\2"+
		"\2\2\u0183\u0184\3\2\2\2\u0184\u0182\3\2\2\2\u0184\u0185\3\2\2\2\u0185"+
		"\u0186\3\2\2\2\u0186\u0188\5F$\2\u0187\u017d\3\2\2\2\u0187\u0182\3\2\2"+
		"\2\u0188E\3\2\2\2\u0189\u018f\5H%\2\u018a\u018f\5J&\2\u018b\u018f\5L\'"+
		"\2\u018c\u018f\5N(\2\u018d\u018f\5P)\2\u018e\u0189\3\2\2\2\u018e\u018a"+
		"\3\2\2\2\u018e\u018b\3\2\2\2\u018e\u018c\3\2\2\2\u018e\u018d\3\2\2\2\u018f"+
		"G\3\2\2\2\u0190\u0191\7\61\2\2\u0191I\3\2\2\2\u0192\u0193\5R*\2\u0193"+
		"K\3\2\2\2\u0194\u0195\7\5\2\2\u0195\u0196\5,\27\2\u0196\u0197\7\7\2\2"+
		"\u0197M\3\2\2\2\u0198\u0199\7.\2\2\u0199O\3\2\2\2\u019a\u019b\7/\2\2\u019b"+
		"\u019c\7\5\2\2\u019c\u019d\5R*\2\u019d\u019e\7\7\2\2\u019eQ\3\2\2\2\u019f"+
		"\u01a0\5T+\2\u01a0S\3\2\2\2\u01a1\u01a2\7\60\2\2\u01a2U\3\2\2\2\61Y_n"+
		"qy|\u0082\u0091\u00a8\u00c4\u00c7\u00d3\u00de\u00e1\u00e9\u00f0\u0103"+
		"\u0105\u010d\u010f\u0117\u0119\u0121\u0123\u012b\u012d\u0135\u0137\u013d"+
		"\u0142\u0144\u014c\u0151\u0153\u0159\u015e\u0160\u0166\u016b\u016d\u0174"+
		"\u0179\u017b\u0182\u0184\u0187\u018e";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}