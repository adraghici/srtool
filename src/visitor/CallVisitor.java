package visitor;

import ast.AssertStmt;
import ast.AssignStmt;
import ast.AssumeStmt;
import ast.BlockStmt;
import ast.CallStmt;
import ast.Expr;
import ast.HavocStmt;
import ast.Node;
import ast.ProcedureDecl;
import ast.Program;
import ast.Stmt;
import ast.VarDeclStmt;
import ast.VarRef;
import ast.VarRefExpr;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import ssa.Scopes;
import tool.SMTUtil;

import java.util.List;
import java.util.Map;

/**
 * Visitor used to implement method calls.
 */
public class CallVisitor implements Visitor {
    private final Scopes scopes;
    private final Map<String, ProcedureDecl> procedures;

    public CallVisitor() {
        scopes = Scopes.withDefault();
        procedures = Maps.newHashMap();
    }

    @Override
    public Node visit(Program program) {
        program.getProcedureDecls().forEach(proc -> procedures.put(proc.getName(), proc));
        return (Node) visitChildren(program);
    }

    @Override
    public Node visit(ProcedureDecl procedureDecl) {
        scopes.enterScope();
        ProcedureDecl result = (ProcedureDecl) visitChildren(procedureDecl);
        scopes.exitScope();
        return result;
    }

    @Override
    public Stmt visit(CallStmt callStmt) {
        List<Stmt> stmts = Lists.newArrayList();
        ProcedureDecl proc = procedures.get(callStmt.getProcedureRef().getName());

        Map<String, Expr> args = createArgReplacements(callStmt, proc);

        // Assert preconditions.
        proc.getPreconditions()
            .forEach(pre -> stmts.add(new AssertStmt((Expr) pre.getCondition().replace(args).accept(this))));

        // Havoc callee modset.
        scopes.topScope().modset(proc.getModified()).forEach(x -> stmts.add(new HavocStmt(new VarRef(x))));

        // Declare and havoc return variable.
        // TODO: Deal with multiple calls to the same function.
        VarRef returnVarRef = new VarRef(proc.getName() + "_ret");
        stmts.add(new VarDeclStmt(returnVarRef));
        stmts.add(new HavocStmt(returnVarRef));

        // Assume postconditions.
        VarRefExpr returnVarRefExpr = new VarRefExpr(returnVarRef);
        proc.getPostconditions()
            .forEach(post -> stmts.add(new AssumeStmt((Expr) post.getCondition().replace(args).accept(this))));

        // Assign result to variable.
        stmts.add(new AssignStmt(callStmt.getVarRef(), returnVarRefExpr));

        return new BlockStmt(stmts);
    }

    @Override
    public Node visit(BlockStmt blockStmt) {
        scopes.enterScope();
        BlockStmt result = (BlockStmt) visitChildren(blockStmt);
        scopes.exitScope();
        return result;
    }

    @Override
    public Node visit(VarRef varRef) {
        scopes.topScope().updateVar(varRef.getVar(), 0);
        return varRef;
    }

    private Map<String, Expr> createArgReplacements(CallStmt callStmt, ProcedureDecl proc) {
        Map<String, Expr> args = Maps.newHashMap();
        args.put(SMTUtil.RESULT_PLACEHOLDER, new VarRefExpr(new VarRef("bar_ret")));
        for (int i = 0; i < callStmt.getArgs().size(); i++) {
            args.put(proc.getParams().get(i).getVar(), (Expr) callStmt.getArgs().get(i).accept(this));
        }
        return args;
    }
}
