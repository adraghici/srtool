package visitor;

import ast.*;
import com.google.common.collect.Lists;

import java.util.List;
import java.util.stream.Collectors;

public interface Visitor {

    default Object visit(Program program) {
        return visitChildren(program);
    }

    default Object visit(VarDeclStmt varDeclStmt) {
        return visitChildren(varDeclStmt);
    }

    default Object visit(ProcedureDecl procedureDecl) {
        return visitChildren(procedureDecl);
    }

    default Object visit(Precondition precondition) {
        return visitChildren(precondition);
    }

    default Object visit(Postcondition postcondition) {
        return visitChildren(postcondition);
    }

    default Object visit(CandidatePrecondition candidatePrecondition) {
        return visitChildren(candidatePrecondition);
    }

    default Object visit(CandidatePostcondition candidatePostcondition) {
        return visitChildren(candidatePostcondition);
    }

    default Object visit(AssignStmt assignStmt) {
        return visitChildren(assignStmt);
    }

    default Object visit(AssertStmt assertStmt) {
        return visitChildren(assertStmt);
    }

    default Object visit(AssumeStmt assumeStmt) {
        return visitChildren(assumeStmt);
    }

    default Object visit(HavocStmt havocStmt) {
        return visitChildren(havocStmt);
    }

    default Object visit(IfStmt ifStmt) {
        return visitChildren(ifStmt);
    }

    default Object visit(WhileStmt whileStmt) {
//        return visitChildren(whileStmt);
        Expr condition = (Expr) whileStmt.getCondition().accept(this);
        BlockStmt whileBlock = (BlockStmt) whileStmt.getWhileBlock().accept(this);
        List<LoopInvariant> invariants =
            whileStmt.getInvariants().stream().map(inv -> (LoopInvariant) inv.accept(this)).collect(Collectors.toList());

        List<Stmt> stmts = whileBlock.getStmts();


        return new WhileStmt(condition, whileBlock, invariants);
    }

    default Object visit(BlockStmt blockStmt) {
        return visitChildren(blockStmt);
    }

    default Object visit(Invariant invariant) {
        return visitChildren(invariant);
    }

    default Object visit(CandidateInvariant candidateInvariant) {
        return visitChildren(candidateInvariant);
    }

    default Object visit(VarRef varRef) {
        return visitChildren(varRef);
    }

    default Object visit(TernaryExpr ternaryExpr) {
        return visitChildren(ternaryExpr);
    }

    default Object visit(BinaryExpr binaryExpr) {
        return visitChildren(binaryExpr);
    }

    default Object visit(UnaryExpr unaryExpr) {
        return visitChildren(unaryExpr);
    }

    default Object visit(NumberExpr numberExpr) {
        return visitChildren(numberExpr);
    }

    default Object visit(VarRefExpr varRefExpr) {
        return visitChildren(varRefExpr);
    }

    default Object visit(ParenExpr parenExpr) {
        return visitChildren(parenExpr);
    }

    default Object visit(ResultExpr resultExpr) {
        return visitChildren(resultExpr);
    }

    default Object visit(OldExpr oldExpr) {
        return visitChildren(oldExpr);
    }

    default Object visitChildren(Node node) {
        List<Node> newChildren = Lists.newArrayList();
        for (Node child : node.getChildren()) {
            //System.out.println("====>>>>> " + child.accept(this));
            Node newChild = (Node) child.accept(this);
            if (newChild != child) {
                newChildren.add(newChild);
            } else {
                newChildren.add(child);
            }
        }
        node.setChildren(newChildren);

        return node;
    }
}
