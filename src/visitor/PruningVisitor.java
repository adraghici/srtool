package visitor;

import ast.BlockStmt;
import ast.Invariant;
import ast.LoopInvariant;
import ast.Node;
import ast.Postcondition;
import ast.PrePostCondition;
import ast.Precondition;
import ast.ProcedureDecl;
import ast.Stmt;
import ast.WhileStmt;
import com.google.common.collect.Lists;
import strategy.Houdini;
import tool.AssertCollector;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Visitor needed to prune preconditions, postconditions, invariants.
 * This is intended to be mainly used for {@link Houdini}.
 */
public class PruningVisitor extends DefaultVisitor {
    private final List<Node> removalCandidates;
    private final Set<Node> artificialConditions;

    public PruningVisitor(
        List<Node> removalCandidates, Set<Node> artificialConditions, AssertCollector assertCollector) {
        super(assertCollector);
        this.removalCandidates = removalCandidates;
        this.artificialConditions = artificialConditions;
    }

    @Override
    public ProcedureDecl visit(ProcedureDecl procedureDecl) {
        List<Precondition> remainingPreconditions =
            procedureDecl.getPreconditions().stream()
                .filter(p -> !removalCandidates.contains(p))
                .map(p -> (Precondition) p.accept(this))
                .collect(Collectors.toList());
        List<Postcondition> remainingPostconditions =
            procedureDecl.getPostconditions().stream()
                .filter(p -> !removalCandidates.contains(p))
                .map(p -> (Postcondition) p.accept(this))
                .collect(Collectors.toList());

        List<PrePostCondition> conditions = Lists.newArrayList();
        conditions.addAll(remainingPreconditions);
        conditions.addAll(remainingPostconditions);

        List<Stmt> stmts = procedureDecl.getStmts().stream()
            .map(stmt -> (Stmt) stmt.accept(this))
            .collect(Collectors.toList());
        return new ProcedureDecl(
            procedureDecl.getName(),
            procedureDecl.getParams(),
            conditions,
            stmts,
            procedureDecl.getReturnExpr());
    }

    @Override
    public WhileStmt visit(WhileStmt whileStmt) {
        List<LoopInvariant> remainingInvariants =
            whileStmt.getInvariants().stream()
                .filter(i -> !removalCandidates.contains(i))
                .map(i -> (Invariant) i.accept(this))
                .collect(Collectors.toList());

        BlockStmt whileBlock = (BlockStmt) whileStmt.getWhileBlock().accept(this);
        return new WhileStmt(whileStmt.getCondition(), whileBlock, remainingInvariants);
    }

    @Override
    public Precondition visit(Precondition precondition) {
        Precondition pre = new Precondition(precondition.getCondition());
        if (artificialConditions.contains(precondition)) {
            artificialConditions.add(pre);
            assertCollector.addOrigin(pre);
        }
        return pre;
    }

    @Override
    public Postcondition visit(Postcondition postcondition) {
        Postcondition post = new Postcondition(postcondition.getCondition());
        if (artificialConditions.contains(postcondition)) {
            artificialConditions.add(post);
            assertCollector.addOrigin(post);
        }
        return post;
    }

    @Override
    public Invariant visit(Invariant invariant) {
        Invariant inv = new Invariant(invariant.getCondition());
        if (artificialConditions.contains(invariant)) {
            artificialConditions.add(inv);
            assertCollector.addOrigin(inv);
        }
        return inv;
    }

    @Override
    public String getDescription() {
        return "Pruning visitor";
    }
}
