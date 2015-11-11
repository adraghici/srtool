package visitor;

import ast.*;

public interface ASTVisitor {

    default Object visitChildren(ast.Node node) {
        for (Node n : node.getChildren()) {
            visit(n);
        }
        return node;
    }

    default Object visit(AssertStmt assertStmt) {
        return visitChildren(assertStmt);
    }

    default Object visit(AssignStmt assignStmt) {
        return visitChildren(assignStmt);
    }

    default Object visit(AssumeStmt assumeStmt) {
        return visitChildren(assumeStmt);
    }

    default Object visit(AtomExpr atomExpr) {
        return visitChildren(atomExpr);
    }

    default Object visit(BinaryExpr binaryExpr) {
        return visitChildren(binaryExpr);
    }

    default Object visit(BlockStmt blockStmt) {
        return visitChildren(blockStmt);
    }

    default Object visit(CandidatePostcondition candidatePostcondition) {
        return visitChildren(candidatePostcondition);
    }

    default Object visit(CandidatePrecondition candidatePrecondition) {
        return visitChildren(candidatePrecondition);
    }

    default Object visit(Expr expr) {
        return visitChildren(expr);
    }

    default Object visit(HavocStmt havocStmt) {
        return visitChildren(havocStmt);
    }

    default Object visit(IfStmt ifStmt) {
        return visitChildren(ifStmt);
    }

    default Object visit(NumberExpr numberExpr) {
        return visitChildren(numberExpr);
    }

    default Object visit(Node node) {
        return null;
    }

    default Object visit(OldExpr oldExpr) {
        return visitChildren(oldExpr);
    }

    default Object visit(ParenExpr parenExpr) {
        return visitChildren(parenExpr);
    }

    default Object visit(Postcondition postcondition) {
        return visitChildren(postcondition);
    }

    default Object visit(Precondition precondition) {
        return visitChildren(precondition);
    }

    default Object visit(PrePostCondition prePostCondition) {
        return visitChildren(prePostCondition);
    }

    default Object visit(ProcedureDecl procedureDecl) {
        return visitChildren(procedureDecl);
    }

    default Object visit(Program program) {
        return visitChildren(program);
    }

    default Object visit(ResultExpr resultExpr) {
        return visitChildren(resultExpr);
    }

    default Object visit(Stmt stmt) {
        return visitChildren(stmt);
    }

    default Object visit(TernaryExpr ternaryExpr) {
        return visitChildren(ternaryExpr);
    }

    default Object visit(UnaryExpr unaryExpr) {
        return visitChildren(unaryExpr);
    }

    default Object visit(VarDeclStmt varDeclStmt) {
        return visitChildren(varDeclStmt);
    }

    default Object visit(VarRef varRef) {
        return visitChildren(varRef);
    }

    default Object visit(VarRefExpr varRefExpr) {
        return visitChildren(varRefExpr);
    }

}
