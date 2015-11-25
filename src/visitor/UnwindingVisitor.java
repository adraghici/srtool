package visitor;

import ast.AssertStmt;
import ast.AssumeStmt;
import ast.BlockStmt;
import ast.Expr;
import ast.IfStmt;
import ast.Node;
import ast.NumberExpr;
import ast.Stmt;
import ast.WhileStmt;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import tool.AssertCollector;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Visitor used to unwind loops. The sound version will additionally collect unwinding assertions.
 */
public class UnwindingVisitor extends DefaultVisitor {
    private final boolean sound;
    private final int depth;
    private final Set<Node> unwindingAsserts;

    public static UnwindingVisitor createUnsound(int depth) {
        return new UnwindingVisitor(depth);
    }

    public static UnwindingVisitor createSound(
        AssertCollector assertCollector,
        Set<Node> unwindingAsserts,
        int depth) {
        return new UnwindingVisitor(assertCollector, unwindingAsserts, depth);
    }

    private UnwindingVisitor(int depth) {
        sound = false;
        this.depth = depth;
        this.unwindingAsserts = Sets.newHashSet();
    }

    private UnwindingVisitor(AssertCollector assertCollector, Set<Node> unwindingAsserts, int depth) {
        super(assertCollector);
        sound = true;
        this.depth = depth;
        this.unwindingAsserts = unwindingAsserts;
    }

    @Override
    public Stmt visit(WhileStmt whileStmt) {
        NumberExpr falseExpr = new NumberExpr("0");
        AssertStmt unwindingAssert = new AssertStmt(falseExpr);
        unwindingAsserts.add(unwindingAssert);
        assertCollector.addOrigin(unwindingAssert);

        List<Stmt> soundBlockStmts = Lists.newArrayList(unwindingAssert, new AssumeStmt(falseExpr));
        List<Stmt> unsoundBlockStmts = Lists.newArrayList(new AssumeStmt(falseExpr));
        List<Stmt> blockStmts = sound ? soundBlockStmts : unsoundBlockStmts;
        IfStmt result = new IfStmt(
            whileStmt.getCondition(),
            new BlockStmt(blockStmts),
            Optional.empty());

        List<Stmt> invariantAsserts = whileStmt.getInvariants().stream()
            .map(inv -> {
                AssertStmt stmt = new AssertStmt(inv.getCondition());
                assertCollector.addOrigin(inv);
                assertCollector.add(inv, stmt);
                return stmt;
            })
            .collect(Collectors.toList());

        for (int i = 0; i < depth; ++i) {
            List<Stmt> ifStmts = whileStmt.getWhileBlock().getStmts().stream()
                .map(stmt -> (Stmt) stmt.accept(this))
                .collect(Collectors.toList());
            List<Stmt> stmts = Lists.newArrayList();
            stmts.addAll(ifStmts);
            stmts.addAll(invariantAsserts);
            stmts.add(result);
            result = new IfStmt(whileStmt.getCondition(), new BlockStmt(stmts), Optional.empty());
        }

        List<Stmt> stms = Lists.newArrayList(invariantAsserts);
        stms.add(result);
        return new BlockStmt(stms);
    }

    @Override
    public Object visit(AssertStmt assertStmt) {
        AssertStmt stmt = new AssertStmt((Expr) assertStmt.getCondition().accept(this));
        assertCollector.addOrigin(assertStmt);
        assertCollector.add(assertStmt, stmt);
        return stmt;
    }

    @Override
    public String getDescription() {
        return "Loop unwinding visitor";
    }
}
