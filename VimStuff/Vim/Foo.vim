Foo: IO ()
Foo = putStrLn "oh boy"

Bar: IO()
Bar = do 
	Foo
	Foo
	putStrLn "here we goasdf"
