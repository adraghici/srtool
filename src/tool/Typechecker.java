package tool;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.BlockStmtContext;
import parser.SimpleCParser.CallStmtContext;
import parser.SimpleCParser.CandidateEnsuresContext;
import parser.SimpleCParser.EnsuresContext;
import parser.SimpleCParser.FormalParamContext;
import parser.SimpleCParser.HavocStmtContext;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import parser.SimpleCParser.ResultExprContext;
import parser.SimpleCParser.VarDeclContext;
import parser.SimpleCParser.VarrefContext;

public class Typechecker extends SimpleCBaseVisitor<Void> {

	private Map<String, Integer> expectedProcedures = new HashMap<>();

	private Map<String, Integer> actualProcedures = new HashMap<>();

	private Set<String> globals = new HashSet<>();

	private HashSet<String> parameters = null;
	
	private List<Set<String>> localsStack = new ArrayList<>();
	
	private List<String> errors = new ArrayList<String>();
	
	private boolean inEnsures = false;

	@Override
	public Void visitProgram(ProgramContext ctx) {
		for(VarDeclContext varDecl : ctx.globals) {
			globals.add(varDecl.ident.name.getText());
		}
		
		for(ProcedureDeclContext proc : ctx.procedures) {
			visit(proc);
		}
		return null;
	}

	@Override
	public Void visitVarDecl(VarDeclContext ctx) {
		String name = ctx.ident.name.getText();
		if(peekLocalsStack().contains(name)) {
			error("Redeclaration of local variable " + name + " at line " + ctx.ident.name.getLine());
		}
		if(localsStack.size() == 1 && parameters.contains(name)) {
			error("Declaration of local variable " + name + " at line " + ctx.ident.name.getLine() + " in root procedure scope may not shadow the name of a parameter");
		}
		
		peekLocalsStack().add(name);
		return super.visitVarDecl(ctx);
	}
	
	@Override
	public Void visitBlockStmt(BlockStmtContext ctx) {
		pushLocalsStack();
		Void result = super.visitBlockStmt(ctx);
		popLocalsStack();
		return result;
	}
	
	@Override
	public Void visitProcedureDecl(ProcedureDeclContext ctx) {
		String name = ctx.name.getText();
		if (actualProcedures.containsKey(name)) {
			error("Redeclaration of procedure " + name + " at line " + ctx.name.getLine());
		}
		actualProcedures.put(name, ctx.formals.size());
		parameters = new HashSet<>();
		pushLocalsStack();
		for(FormalParamContext fp : ctx.formals) {
			String formalParamName = fp.ident.name.getText();
			if(parameters.contains(formalParamName)) {
				error("Duplicate declaration of parameter " + formalParamName + " at line " + fp.ident.name.getLine());
			}
			parameters.add(formalParamName);
		}
		Void result = super.visitProcedureDecl(ctx);
		popLocalsStack();
		parameters = null;
		return result;
	}
	
	@Override
	public Void visitEnsures(EnsuresContext ctx) {
		inEnsures = true;
		Void result = super.visitEnsures(ctx);
		inEnsures = false;
		return result;
	}

	@Override
	public Void visitCandidateEnsures(CandidateEnsuresContext ctx) {
		inEnsures = true;
		Void result = super.visitCandidateEnsures(ctx);
		inEnsures = false;
		return result;
	}
	
	@Override
	public Void visitResultExpr(ResultExprContext ctx) {
		if(!inEnsures) {
			error("'\\result' appears outside 'ensures' clause at line " + ctx.resultTok.getLine());
		}
		return super.visitResultExpr(ctx);
	}

	@Override
	public Void visitOldExpr(parser.SimpleCParser.OldExprContext ctx) {
		if(!globals.contains(ctx.arg.ident.name.getText()) || parameters.contains(ctx.arg.ident.getText())) {
			error("'\\old' applied to non-global variable at line " + ctx.oldTok.getLine());
		}
		return super.visitOldExpr(ctx);
	}
	
	@Override
	public Void visitCallStmt(CallStmtContext ctx) {
		String name = ctx.callee.getText();
		int numArgs = ctx.actuals.size();
		if(expectedProcedures.containsKey(name) && expectedProcedures.get(name) != numArgs) {
			error("Procedure " + name + " is called inconsistently at line " + ctx.callee.getLine());
		}
		expectedProcedures.put(name, numArgs);
		checkAssignmentToVar(ctx.lhs);
		return super.visitCallStmt(ctx);
	}
	
	@Override
	public Void visitVarref(VarrefContext ctx) {
		String name = ctx.ident.name.getText();
		if(!isLocalVariable(name) && !parameters.contains(name) && !globals.contains(name)) {
			error("Undefined variable " + name + " referenced at line " + ctx.ident.name.getLine());
		}
		return super.visitVarref(ctx);
	}

	private boolean isLocalVariable(String name) {
		boolean foundLocally = false;
		for(int i = localsStack.size() - 1; i >= 0; i--) {
			if(localsStack.get(i).contains(name)) {
				foundLocally = true;
				break;
			}
		}
		return foundLocally;
	}
		
	private Set<String> peekLocalsStack() {
		return localsStack.get(localsStack.size() - 1);
	}
	
	private Set<String> popLocalsStack() {
		return localsStack.remove(localsStack.size() - 1);
	}

	private void pushLocalsStack() {
		pushLocalsStack(new HashSet<String>());
	}

	private void pushLocalsStack(Set<String> frame) {
		localsStack.add(frame);
	}
		
	public void resolve() {
		for(String callee : expectedProcedures.keySet()) {
			if(actualProcedures.containsKey(callee)) {
				if(expectedProcedures.get(callee) != actualProcedures.get(callee)) {
					error("Procedure " + callee + " invoked with " + expectedProcedures.get(callee) + " arguments, but " + actualProcedures.get(callee) + " were expected");
				}
			} else {
				error("Procedure " + callee + " called but not declared");
			}
		}
	}
	
	@Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
		checkAssignmentToVar(ctx.lhs);
		return super.visitAssignStmt(ctx);
	}

	@Override
	public Void visitHavocStmt(HavocStmtContext ctx) {
		checkAssignmentToVar(ctx.var);
		return super.visitHavocStmt(ctx);
	}

	private void checkAssignmentToVar(VarrefContext var) {
		String receivingName = var.ident.name.getText();
		if(!isLocalVariable(receivingName) && parameters.contains(receivingName)) {
			error("Attempt to modify parameter " + receivingName + " at line " + var.ident.name.getLine());
		}
	}
	
	private void error(String errorString) {
		errors.add(errorString);
	}

	public boolean hasErrors() {
		return !errors.isEmpty();
	}

	public Iterable<String> getErrors() {
		return errors;
	}
	
}


                                         