package visitor;

import ast.*;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import ssa.Scopes;
import tool.AssertCollector;
import tool.SMTUtil;

import java.util.List;
import java.util.Map;

/**
 * Visitor used to implement method calls.
 */
public class CallVisitor extends DefaultVisitor {
    private final Scopes scopes;
    private final Map<String, ProcedureDecl> procedures;
    private boolean inCallStmt;
    private final AssertCollector assertCollector;

    public CallVisitor(AssertCollector assertCollector) {
        scopes = Scopes.withDefault();
        procedures = Maps.newHashMap();
        sourceType = TraceableNode.SourceType.CALL;
        this.assertCollector = assertCollector;
    }

    @Override
    public Node visit(Program program) {
        program.getProcedureDecls().forEach(proc -> procedures.put(proc.getName(), proc));
        return (Node) super.visit(program);
    }

    @Override
    public Node visit(ProcedureDecl procedureDecl) {
        scopes.enterScope();
        ProcedureDecl result = (ProcedureDecl) super.visit(procedureDecl);
        scopes.exitScope();
        return result;
    }

    @Override
    public Stmt visit(CallStmt callStmt) {
        inCallStmt = true;
        List<Stmt> stmts = Lists.newArrayList();
        ProcedureDecl proc = procedures.get(callStmt.getProcedureRef().getName());
        Map<String, Expr> substituteArgs = createSubstituteArgs(callStmt, proc);

        // Assert preconditions and candidate preconditions.
        proc.getPreconditions()
            .forEach(pre -> stmts.add(
                new AssertStmt((Expr) pre.getCondition().replace(substituteArgs).accept(this))));
        proc.getCandidatePreconditions().forEach(pre -> {
            AssertStmt assertStmt =
                new AssertStmt((Expr) pre.getCondition().replace(substituteArgs).accept(this));
            stmts.add(assertStmt);
            assertCollector.add(pre, assertStmt);
        });

        // Havoc callee modset.
        scopes.topScope().modset(proc.getModified())
            .forEach(modified -> stmts.add(new HavocStmt(new VarRef(modified))));

        // Declare and havoc return variable.
        VarRef returnVarRef = new VarRef(returnVarName(proc.getName()));
        stmts.add(new VarDeclStmt(returnVarRef));
        stmts.add(new HavocStmt(returnVarRef));

        // Assume postconditions.
        VarRefExpr returnVarRefExpr = new VarRefExpr(returnVarRef);
        proc.getPostconditions()
            .forEach(post -> stmts.add(
                new AssumeStmt((Expr) post.getCondition().replace(substituteArgs).accept(this))));

        // Assign result to variable.
        stmts.add(new AssignStmt(callStmt.getVarRef(), returnVarRefExpr));
        inCallStmt = false;

        return new BlockStmt(stmts);
    }

    @Override
    public Node visit(BlockStmt blockStmt) {
        scopes.enterScope();
        BlockStmt result = (BlockStmt) super.visit(blockStmt);
        scopes.exitScope();
        return result;
    }

    @Override
    public Node visit(VarRef varRef) {
        scopes.topScope().updateVar(varRef.getVar(), 0);
        return varRef;
    }

    @Override
    public Node visit(OldExpr oldExpr) {
        if (inCallStmt) {
            return new VarRefExpr((VarRef) oldExpr.getVarRef().accept(this));
        }
        return (OldExpr) super.visit(oldExpr);
    }

    @Override
    public String getDescription() {
        return "Call visitor";
    }

    /**
     * Builds a map from argument names of a {@link ProcedureDecl} to the actual expressions of a given
     * {@link CallStmt} to allow substitution of arguments in pre and post conditions with the
     * actual expressions passed in the procedure call.
     */
    private Map<String, Expr> createSubstituteArgs(CallStmt callStmt, ProcedureDecl proc) {
        Map<String, Expr> substitutes = Maps.newHashMap();
        substitutes.put(
            SMTUtil.RESULT_PLACEHOLDER, new VarRefExpr(new VarRef(returnVarName(proc.getName()))));
        for (int i = 0; i < callStmt.getArgs().size(); ++i) {
            substitutes.put(
                proc.getParams().get(i).getVar(), (Expr) callStmt.getArgs().get(i).accept(this));
        }
        return substitutes;
    }

    private static String returnVarName(String var) {
        return var + "_ret";
    }
}
