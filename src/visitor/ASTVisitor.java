package visitor;

import ast.*;

public interface ASTVisitor {

    default public Object visitChildren(ast.Node node) {
        for (Node n : node.getChildren()) {
            System.out.println(n.getClass());
            visit(n);
        }
        return node;
    }

    default Object visit(AssertStmt assertStmt) {
        return visitChildren(assertStmt);
    }

    default public Object visit(AssignStmt assignStmt) {
        return visitChildren(assignStmt);
    }

    default public Object visit(AssumeStmt assumeStmt) {
        return visitChildren(assumeStmt);
    }

    default public Object visit(BinaryExpr binaryExpr) {
        return visitChildren(binaryExpr);
    }

    default public Object visit(BlockStmt blockStmt) {
        return visitChildren(blockStmt);
    }

    default public Object visit(CandidatePostcondition candidatePostcondition) {
        return visitChildren(candidatePostcondition);
    }

    default public Object visit(CandidatePrecondition candidatePrecondition) {
        return visitChildren(candidatePrecondition);
    }

    default public Object visit(HavocStmt havocStmt) {
        return visitChildren(havocStmt);
    }

    default public Object visit(IfStmt ifStmt) {
        return visitChildren(ifStmt);
    }

    default public Object visit(NumberExpr numberExpr) {
        return visitChildren(numberExpr);
    }

    default public Object visit(Node node) {
        return null;
    }

    default public Object visit(OldExpr oldExpr) {
        return visitChildren(oldExpr);
    }

    default public Object visit(ParenExpr parenExpr) {
        return visitChildren(parenExpr);
    }

    default public Object visit(Postcondition postcondition) {
        return visitChildren(postcondition);
    }

    default public Object visit(Precondition precondition) {
        return visitChildren(precondition);
    }

    default public Object visit(ProcedureDecl procedureDecl) {
        return visitChildren(procedureDecl);
    }

    default public Object visit(Program program) {
        return visitChildren(program);
    }

    default public Object visit(ResultExpr resultExpr) {
        return visitChildren(resultExpr);
    }

    default public Object visit(TernaryExpr ternaryExpr) {
        return visitChildren(ternaryExpr);
    }

    default public Object visit(UnaryExpr unaryExpr) {
        return visitChildren(unaryExpr);
    }

    default public Object visit(VarDeclStmt varDeclStmt) {
        return visitChildren(varDeclStmt);
    }

    default public Object visit(VarRefExpr varRefExpr) {
        return visitChildren(varRefExpr);
    }
}
