package js;

import javax.script.Invocable;
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;

public class TaintJSJavaTestClass {
    private static int staticField;

    private int instanceField;

    public static void main (String[] args) throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");
        try {
            se.eval("function check(str) {\n" +
                    "    return str === \"1337\";\n" +
                    "}");
        } catch (ScriptException e) {
            // never happens
        }
        String pw = source();

        Invocable inv = (Invocable) se;
        try {
            Boolean state = (Boolean) inv.invokeFunction("check", pw);
            sink(state);
        } catch (NoSuchMethodException e) {
            // never happens
        }
    }

    public static String source() {
        return "1337";
    }

    private static int sanitize(int i) {return i;}

    private static void sink(int i) {
        System.out.println(i);
    }
    private static void sink(boolean i) {
    System.out.println(i);
    }
}
