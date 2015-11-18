package visitor;

import ast.BlockStmt;
import ast.CandidateInvariant;
import ast.CandidatePostcondition;
import ast.CandidatePrecondition;
import ast.LoopInvariant;
import ast.Node;
import ast.PrePostCondition;
import ast.ProcedureDecl;
import ast.Stmt;
import ast.TraceableNode.SourceType;
import ast.WhileStmt;
import com.google.common.collect.Lists;

import java.util.List;
import java.util.stream.Collectors;

public class RemovingVisitor extends DefaultVisitor {
    private final List<Node> removalCandidates;

    public RemovingVisitor(List<Node> removalCandidates) {
        sourceType = SourceType.REMOVING;
        this.removalCandidates = removalCandidates;
    }

    @Override public Object visit(ProcedureDecl procedureDecl) {
        List<CandidatePrecondition> remainingCandidatePreconditions =
            procedureDecl.getCandidatePreconditions().stream()
                .filter(p -> !removalCandidates.contains(p))
                .map(p -> (CandidatePrecondition) super.visit(p))
                .collect(Collectors.toList());
        List<CandidatePostcondition> remainingCandidatePostconditions =
            procedureDecl.getCandidatePostconditions().stream()
                .filter(p -> !removalCandidates.contains(p))
                .map(p -> (CandidatePostcondition) super.visit(p))
                .collect(Collectors.toList());

        List<PrePostCondition> conditions = Lists.newArrayList();
        conditions.addAll(procedureDecl.getPreconditions());
        conditions.addAll(remainingCandidatePreconditions);
        conditions.addAll(procedureDecl.getPostconditions());
        conditions.addAll(remainingCandidatePostconditions);

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

    @Override public Object visit(WhileStmt whileStmt) {
        List<CandidateInvariant> remainingCandidateInvariants =
            whileStmt.getCandidateInvariants().stream()
                .filter(i -> !removalCandidates.contains(i))
                .map(i -> (CandidateInvariant) super.visit(i))
                .collect(Collectors.toList());

        List<LoopInvariant> loopInvariants = Lists.newArrayList();
        loopInvariants.addAll(whileStmt.getInvariants());
        loopInvariants.addAll(remainingCandidateInvariants);

        BlockStmt whileBlock = (BlockStmt) whileStmt.getWhileBlock().accept(this);
        return new WhileStmt(whileStmt.getCondition(), whileBlock, loopInvariants);
    }
}
