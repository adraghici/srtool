package ast;

public class ResultExpr implements AtomExpr {
    private final String token;

    public ResultExpr(String token) {
        this.token = token;
    }

    public String getToken() {
        return token;
    }
}
