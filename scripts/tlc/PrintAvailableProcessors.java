final class PrintAvailableProcessors {
    private PrintAvailableProcessors() {}

    public static void main(String[] args) {
        System.out.println(Runtime.getRuntime().availableProcessors());
    }
}
