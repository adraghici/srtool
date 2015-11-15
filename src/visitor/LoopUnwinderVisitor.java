package visitor;

import ast.*;
import com.google.common.collect.Lists;
import ssa.Scopes;

import java.util.List;
import java.util.Optional;

/**
 * Visitor used to replace while loops with invariant assertions, randomising variables and if statements.
 */
public class LoopUnwinderVisitor implements Visitor {
    private final Scopes scopes;
    private final int depth;

    public LoopUnwinderVisitor() {
        this.scopes = Scopes.withDefault();
        depth = 3;
    }

    @Override public Node visit(ProcedureDecl procedureDecl) {
        scopes.enterScope();
        ProcedureDecl result = (ProcedureDecl) visitChildren(procedureDecl);
        scopes.exitScope();
        return result;
    }

    @Override public Stmt visit(WhileStmt whileStmt) {
        Expr whileCondition = whileStmt.getCondition();

        IfStmt result = new IfStmt(
            whileCondition,
            new BlockStmt(Lists.newArrayList(new AssumeStmt(new NumberExpr("0")))),
            Optional.empty());

        for (int i = 1; i <= depth; i++) {
            List<Stmt> ifStmts = Lists.newArrayList(whileStmt.getWhileBlock().getStmts());
            ifStmts.add(result);
            result = new IfStmt(whileCondition, new BlockStmt(ifStmts), Optional.empty());
        }

        return result;
    }

    @Override public Node visit(BlockStmt blockStmt) {
        scopes.enterScope();
        BlockStmt result = (BlockStmt) visitChildren(blockStmt);
        scopes.exitScope();
        return result;
    }

    @Override public Node visit(VarRef varRef) {
        scopes.topScope().updateVar(varRef.getVar(), 0);
        return varRef;
    }
}
