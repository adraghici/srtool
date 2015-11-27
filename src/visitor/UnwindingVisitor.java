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
import strategy.BMC;
import tool.NodeCollector;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Visitor used to unwind loops. The sound version will additionally collect unwinding assertions.
 */
public class UnwindingVisitor extends DefaultVisitor {
    private final boolean sound;
    private final Set<Node> unwindingAsserts;
    private final Map<Node, Integer> unwindingDepths;
    private final Map<Node, Node> assertLocations;

    public UnwindingVisitor(
        NodeCollector nodeCollector,
        Map<Node, Integer> unwindingDepths,
        Set<Node> unwindingAsserts,
        Map<Node, Node> assertLocations,
        boolean sound) {
        super(nodeCollector);
        this.sound = sound;
        this.unwindingAsserts = unwindingAsserts;
        this.unwindingDepths = unwindingDepths;
        this.assertLocations = assertLocations;
    }

    @Override
    public Stmt visit(WhileStmt whileStmt) {
        Node loop = nodeCollector.resolve(whileStmt);
        unwindingDepths.putIfAbsent(loop, BMC.INITIAL_DEPTH);
        int depth = unwindingDepths.get(loop);

        NumberExpr falseExpr = new NumberExpr("0");
        AssertStmt unwindingAssert = new AssertStmt(falseExpr);
        unwindingAsserts.add(unwindingAssert);
        nodeCollector.addOrigin(unwindingAssert);
        assertLocations.put(unwindingAssert, nodeCollector.resolve(whileStmt));

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
                nodeCollector.addOrigin(inv);
                nodeCollector.add(inv, stmt);
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
        nodeCollector.addOrigin(assertStmt);
        nodeCollector.add(assertStmt, stmt);
        return stmt;
    }

    @Override
    public String getDescription() {
        return "Loop unwinding visitor";
    }
}
