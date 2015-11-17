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
import ast.TraceableNode.SourceType;
import ast.VarRef;
import ast.WhileStmt;
import com.google.common.collect.Lists;
import ssa.Scopes;
import tool.AssertCollector;

import java.util.List;
import java.util.Optional;

/**
 * Visitor used to replace while loops with invariant assertions, randomising variables and if statements.
 */
public class WhileVisitor extends DefaultVisitor {
    private final Scopes scopes;
    private final AssertCollector assertCollector;

    public WhileVisitor(AssertCollector assertCollector) {
        this.scopes = Scopes.withDefault();
        this.assertCollector = assertCollector;
        sourceType = SourceType.WHILE;
    }

    @Override
    public Node visit(ProcedureDecl procedureDecl) {
        scopes.enterScope();
        ProcedureDecl result = (ProcedureDecl) super.visit(procedureDecl);
        scopes.exitScope();
        return result;
    }

    @Override
    public Stmt visit(WhileStmt whileStmt) {
        List<Stmt> stmts = Lists.newArrayList();

        whileStmt.getLoopInvariants().forEach(x -> stmts.add(new AssertStmt(x.getCondition())));
        whileStmt.getCandidateInvariants().forEach(i -> {
            AssertStmt assertStmt = new AssertStmt(i.getCondition());
            stmts.add(assertStmt);
            assertCollector.add(i, assertStmt);
        });

        scopes.topScope().modset(whileStmt.getModified()).forEach(x -> stmts.add(new HavocStmt(new VarRef(x))));
        whileStmt.getLoopInvariants().forEach(x -> stmts.add(new AssumeStmt(x.getCondition())));

        List<Stmt> ifStmts = Lists.newArrayList();
        whileStmt.getWhileBlock().getStmts().forEach(stmt -> ifStmts.add((Stmt) stmt.accept(this)));
        whileStmt.getInvariants().forEach(x -> ifStmts.add(new AssertStmt(x.getCondition())));
        ifStmts.add(new AssumeStmt(new NumberExpr("0")));

        whileStmt.getCandidateInvariants().forEach(i -> {
            AssertStmt assertStmt = new AssertStmt(i.getCondition());
            ifStmts.add(assertStmt);
            assertCollector.add(i, assertStmt);
        });

        stmts.add(new IfStmt(whileStmt.getCondition(), new BlockStmt(ifStmts), Optional.empty()));

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
    public String getDescription() {
        return "While visitor";
    }
}
