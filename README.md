# Тайпчекер для просто типизированного и полиморфного лямбда-исчислений

Проект выполнен для отбора на студенческую смену МКН в Сириусе по формальной верефикации студентом 4 курса Рябковым Антоном.

## О проекте
Проект выполнен на языке `Haskell`, в качестве сборщика двух получившихся проектов выступает `Cabal`. 

Так же для репозитория настроен `CI`, который автоматически запускает тесты для каждой из веток. Тесты сделаны с использованием библиотеки `HUnit` и их запускает сам `Cabal` через встроенную систему тестирования.

Более подробно о самих тестах и особенностях работы чекера можно узнать в `README.md` в ветке каждого из проектов.

## Стуктура проекта 
Тайпчекер для просто типизированного лямбда-исчисления находится в ветке данного репозитория под названием `simply-typed`. 

В процессе разработки была получена версия для просто типизированного лямбда-исчисления из уже созданного мною год назад эвалюатора для безтипового лямбда-исчисления, но код громоздкий, с кучей ненужных фичей, так что он просто лежит в ветке `typeless-lambda`, чтобы не пропадал.

## Локальное тестирование
Код тестов можно найти в папке `test`, каждый тест прокомментирован тем, какой терм проверяется. Запустить проверку можно командой `cabal v2-test` в корне проекта, это запустит все тест сьюиты и выдаст некоторые логи. Подробность логов можно менять флагом `--verbose` так, что при `--verbose=0` выведутся только сообщения о сьюитах, которые не прошли проверку (если есть), а при `--verbose=2` будет наиболее подробный вывод.
