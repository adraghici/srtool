package visitor;

import ast.AssertStmt;
import ast.AssumeStmt;
import ast.BlockStmt;
import ast.HavocStmt;
import ast.IfStmt;
import ast.Node;
import ast.NumberExpr;
import ast.ProcedureDecl;
import ast.Stmt;
import ast.VarRef;
import ast.WhileStmt;
import com.google.common.collect.Lists;
import ssa.Scopes;

import java.util.List;
import java.util.Optional;

/**
 * Visitor used to replace while loops with invariant assertions, randomising variables and if statements.
 */
public class WhileVisitor implements Visitor {
    private final Scopes scopes;

    public WhileVisitor() {
        this.scopes = Scopes.withDefault();
    }

    @Override
    public Node visit(ProcedureDecl procedureDecl) {
        scopes.enterScope();
        ProcedureDecl result = (ProcedureDecl) visitChildren(procedureDecl);
        scopes.exitScope();
        return result;
    }

    @Override
    public Stmt visit(WhileStmt whileStmt) {
        List<Stmt> stmts = Lists.newArrayList();

        whileStmt.getInvariants().forEach(x -> stmts.add(new AssertStmt(x.getCondition())));
        scopes.topScope().modset(whileStmt.getModified()).forEach(x -> stmts.add(new HavocStmt(new VarRef(x))));
        whileStmt.getInvariants().forEach(x -> stmts.add(new AssumeStmt(x.getCondition())));

        List<Stmt> ifStmts = Lists.newArrayList();
        whileStmt.getWhileBlock().getStmts().forEach(stmt -> ifStmts.add((Stmt) stmt.accept(this)));
        whileStmt.getInvariants().forEach(x -> ifStmts.add(new AssertStmt(x.getCondition())));
        ifStmts.add(new AssumeStmt(new NumberExpr("0")));

        stmts.add(new IfStmt(whileStmt.getCondition(), new BlockStmt(ifStmts), Optional.empty()));

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

    @Override
    public String getDescription() {
        return "While visitor";
    }
}
